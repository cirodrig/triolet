{-| Expressions representing side-effect-free computations.
These expressions are used in common subexpression elimination.
-}

{-# LANGUAGE TypeFamilies, FlexibleContexts, Rank2Types, ScopedTypeVariables #-}
module LowLevel.Expr
       (CSEVal, fromCSEVal,
        Expr, varExpr, litExpr,
        pprExpr,
        exprToCSEVal,
        CSEEnv,
        pprCSEEnv,
        emptyCSEEnv,
        updateCSEEnv,
        cseFindVar,
        cseFindExpr,
        interpretVal,
        interpretPrim,
        interpretStore,
        isZeroAtomExpr,
        isOneAtomExpr,
        generateExprAtom
       )
where

import Prelude hiding(lookup)

import Control.Monad
import Control.Monad.Writer
import qualified Data.List as List
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Debug.Trace
import Text.PrettyPrint.HughesPJ hiding(empty)

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Supply
import LowLevel.Build
import LowLevel.CodeTypes
import LowLevel.Syntax
import LowLevel.Print

-- | A value that CSE may substitute for some other expression.
data CSEVal = CSEVar !Var | CSELit !Lit

-- | Convert a CSE value to a value.
fromCSEVal :: CSEVal -> Val
fromCSEVal (CSEVar v) = VarV v
fromCSEVal (CSELit l) = LitV l

-- | Convert a CSE value to an expression.
-- The expression should be in simplified form.
cseValToExpr :: CSEVal -> Expr
cseValToExpr (CSEVar v) = VarExpr v
cseValToExpr (CSELit l) = LitExpr l

-- | Convert an expression to a CSE value, if it can be so represented.
exprToCSEVal :: Expr -> Maybe CSEVal
exprToCSEVal (VarExpr v) = Just $ CSEVar v
exprToCSEVal (LitExpr l) = Just $ CSELit l
exprToCSEVal _           = Nothing

-- | A commutative and associative operator.
data CAOp =
    AddZOp !Signedness !Size
    deriving(Eq, Ord)

-- | A binary operator.
data BinOp =
    ModZOp !Signedness !Size
  | AddPOp
    deriving(Eq, Ord)

-- | A unary operator.
data UnOp =
    LoadOp !ValueType
  | NegateZOp !Signedness !Size
    deriving(Eq, Ord)

-- | A pure expression.
data Expr =
    VarExpr !Var
  | LitExpr !Lit
  | CAExpr !CAOp [Expr]
  | BinExpr !BinOp Expr Expr
  | UnExpr !UnOp Expr

varExpr :: Var -> Expr
varExpr = VarExpr

litExpr :: Lit -> Expr
litExpr = LitExpr

isIntLitExpr :: Integer -> Expr -> Bool
isIntLitExpr n (LitExpr (IntL _ _ m)) = m == n
isIntLitExpr _ _ = False

exprType :: Expr -> ValueType
exprType = undefined

-- | Unpack a load expression into subexpressions corresponding to the
--   operands of a load instruction.
unpackLoadExpr :: Expr -> Maybe (ValueType, Expr, Integer)
unpackLoadExpr (UnExpr (LoadOp ty) arg) =
  let (base, offset) =
        case arg
        of CAExpr (AddZOp _ _) [e1, e2]
             | LitExpr (IntL _ _ offset) <- e2 -> (e1, offset)
             | LitExpr (IntL _ _ offset) <- e1 -> (e2, offset)
           _ -> (arg, 0)
  in Just (ty, base, offset)

unpackLoadExpr _ = Nothing

pprInfixCAOp (AddZOp _ _) = text "+"

pprBinOp (ModZOp _ _) = text "mod"
pprBinOp AddPOp = text "addp"

pprUnOp (LoadOp _) = text "load"
pprUnOp (NegateZOp _ _) = text "negate"

pprExprParens (VarExpr v) = pprVar v
pprExprParens (LitExpr l) = pprLit l
pprExprParens e = parens $ pprExpr e

pprExpr (VarExpr v) = pprVar v
pprExpr (LitExpr l) = pprLit l
pprExpr (CAExpr op []) = parens $ text "unit" <+> pprInfixCAOp op
pprExpr (CAExpr op args) = foldr1 (\x y -> x <+> pprInfixCAOp op <+> y) $
                           map pprExprParens args
pprExpr (BinExpr op l r) = pprBinOp op <+> pprExprParens l <+> pprExprParens r
pprExpr (UnExpr op e) = pprUnOp op <+> pprExprParens e


-- | A lookup trie for matching expressions.
--
-- There is one field for each 'Expr' constructor.
data TrieNode v =
  TrieNode
  { tVar :: Map.Map Var v
  , tLit :: Map.Map Lit v
  , tCA  :: Map.Map CAOp (ListTrie TrieNode v)
  , tBin :: Map.Map BinOp (TrieNode (TrieNode v))
  , tUn  :: Map.Map UnOp (TrieNode v)
  }

data ListTrie t v = ListTrie !(Maybe v) (t (ListTrie t v))

class Trie t where
  type Key t
  empty :: t v
  toList :: t v -> [(Key t, v)]
  alter :: (Maybe v -> Maybe v) -> Key t -> t v -> t v
  insert :: Key t -> v -> t v -> t v
  insert k v = alter (const (Just v)) k
  lookup :: Key t -> t v -> Maybe v
  mapMaybeWithKey :: (Key t -> v -> Maybe v) -> t v -> t v
  filterKeys :: (Key t -> Bool) -> t v -> t v
  filterKeys f = mapMaybeWithKey (\k v -> if f k then Just v else Nothing)

alterSub :: (Trie t, Trie t') =>
            Key t' -> (t v -> t v) -> t' (t v) -> t' (t v)
alterSub k f = alter (Just . f . fromMaybe empty) k

mapMaybeSub :: (Trie t, Trie t') =>
               (k -> v -> Maybe v)
            -> (Key t' -> Key t -> k)
            -> t' (t v) -> t' (t v)
mapMaybeSub f g = mapMaybeWithKey (\k -> Just . mapMaybeWithKey (f . g k))

mapMaybeSub2 :: (Trie t, Trie t', Trie t'') =>
               (k -> v -> Maybe v)
            -> (Key t'' -> Key t' -> Key t -> k)
            -> t'' (t' (t v)) -> t'' (t' (t v))
mapMaybeSub2 f g =
  mapMaybeWithKey (\k'' -> Just . mapMaybeWithKey (\k' -> Just . mapMaybeWithKey (\k -> f (g k'' k' k))))

instance Ord k => Trie (Map.Map k) where
  type Key (Map.Map k) = k
  empty = Map.empty
  toList = Map.toList
  alter = Map.alter
  insert = Map.insert
  lookup = Map.lookup
  mapMaybeWithKey = Map.mapMaybeWithKey
  filterKeys f m = Map.filterWithKey (\k _ -> f k) m

instance Trie t => Trie (ListTrie t) where
  type Key (ListTrie t) = [Key t]
  empty = ListTrie Nothing empty
  
  toList (ListTrie elem subtrie) =
    let elem_list = case elem
                    of Nothing -> []
                       Just x -> [([], x)]
        subtrie_list = [ (k : ks, v) | (k, next_trie) <- toList subtrie
                                     , (ks, v) <- toList next_trie]
    in elem_list ++ subtrie_list

  alter f ks (ListTrie elem subtrie) =
    case ks
    of []    -> ListTrie (f elem) subtrie
       k:ks' -> ListTrie elem (alterSub k (alter f ks') subtrie)

  insert ks v (ListTrie elem subtrie) =
    case ks
    of []    -> ListTrie (Just v) subtrie
       k:ks' -> ListTrie elem (alterSub k (insert ks' v) subtrie)

  lookup ks (ListTrie elem subtrie) =
    case ks
    of []    -> elem
       k:ks' -> lookup ks' =<< lookup k subtrie
  
  mapMaybeWithKey f (ListTrie elem subtrie) =
    let elem'    = f [] =<< elem
        subtrie' = mapMaybeSub f (:) subtrie
    in ListTrie elem' subtrie'

instance Trie TrieNode where
  type Key TrieNode = Expr
  empty = 
    TrieNode
    { tVar = empty
    , tLit = empty
    , tCA = empty
    , tBin = empty
    , tUn = empty
    }
  toList (TrieNode var_t lit_t ca_t bin_t un_t) =
    [(VarExpr var, v)  | (var, v) <- toList var_t] ++
    [(LitExpr lit, v)  | (lit, v) <- toList lit_t] ++
    [(CAExpr op es, v) | (op, m) <- toList ca_t, (es, v) <- toList m] ++
    [(BinExpr op l r, v) | (op, m1) <- toList bin_t
                         , (l, m2) <- toList m1
                         , (r, v) <- toList m2] ++
    [(UnExpr op e, v) | (op, m) <- toList un_t
                      , (e, v) <- toList m]
  alter f k tr = updateTrieNode (alter f) k tr
  insert k v tr = updateTrieNode (\k -> insert k v) k tr
  lookup k tr =
    case k
    of VarExpr var -> lookup var $ tVar tr
       LitExpr lit -> lookup lit $ tLit tr
       CAExpr op es -> lookup2 op es $ tCA tr
       BinExpr op e1 e2 -> lookup3 op e1 e2 $ tBin tr
       UnExpr op e -> lookup2 op e $ tUn tr
    where
      lookup2 k1 k2 = lookup k2 <=< lookup k1
      lookup3 k1 k2 k3 = lookup k3 <=< lookup k2 <=< lookup k1

  mapMaybeWithKey f tr =
    tr { tVar = mapMaybeWithKey (f . VarExpr) $ tVar tr
       , tLit = mapMaybeWithKey (f . LitExpr) $ tLit tr
       , tCA  = mapMaybeSub f CAExpr $ tCA tr
       , tBin = mapMaybeSub2 f BinExpr $ tBin tr
       , tUn  = mapMaybeSub f UnExpr $ tUn tr}

updateTrieNode :: (forall t'. Trie t' => Key t' -> t' v -> t' v) -> Expr
               -> TrieNode v -> TrieNode v
updateTrieNode f k tr =
  case k
  of VarExpr var -> tr {tVar = f var $ tVar tr}
     LitExpr lit -> tr {tLit = f lit $ tLit tr}
     CAExpr op es -> tr {tCA = alter2 op es $ tCA tr}
     BinExpr op e1 e2 -> tr {tBin = alter3 op e1 e2 $ tBin tr}
     UnExpr op e -> tr {tUn = alter2 op e $ tUn tr}
  where
    alter3 k1 k2 k3 = alterSub k1 $ alterSub k2 $ f k3
    alter2 k1 k2 = alterSub k1 $ f k2

-------------------------------------------------------------------------------

-- | A CSE environment maps expressions to simpler expressions, usually values.
data CSEEnv =
  CSEEnv { -- | Available variable values
           available :: TrieNode CSEVal
           -- | Actual values of variables, indexed by variable ID
         , valuation :: IntMap.IntMap Expr
         }

pprCSEEnv :: CSEEnv -> Doc
pprCSEEnv env =
  text "available:" <+> vcat [pprExpr e <+> text "->" <+> pprVal (fromCSEVal v)
                             | (e, v) <- toList $ available env] $$
  text "valuation:" <+> vcat [text (show n) <+> text "->" <+> pprExpr e 
                             | (n, e) <- IntMap.toList $ valuation env]
  

emptyCSEEnv :: CSEEnv
emptyCSEEnv = CSEEnv empty IntMap.empty

-- | Given a variable and its value, add a mapping to the environment.
updateCSEEnv :: Var -> Expr -> CSEEnv -> CSEEnv
updateCSEEnv v expr env =
  let avail =
        case exprToCSEVal expr
        of Just v_val ->
             -- The variable is equivalent to another variable or constant.
             -- Replace the variable with its equivalent value.
             insert (VarExpr v) v_val $ available env
           Nothing ->
             -- The more complicated expression is equivalent to the variable.
             -- Replace equal values with the variable, unless there's already
             -- a binding there.
             alter (Just . fromMaybe (CSEVar v)) expr $ available env
  in env { available = avail
         , valuation = IntMap.insert (fromIdent $ varID v) expr $ valuation env
         }

-- | Find an available value that's equal to the given variable.  If no value
-- is found, return the variable.
cseFindVar :: Var -> CSEEnv -> CSEVal
cseFindVar v env =
  -- First get the variable's value as an expression.
  -- Return the CSE-preferred value equivalent to that expression,
  -- or else the value itself,
  -- or else the variable.
  let expr = fromMaybe (VarExpr v) $ cseGetValue v env
  in fromMaybe (CSEVar v) $ cseFindExpr expr env `mplus` exprToCSEVal expr

-- | Find an available value that's equal to the given expression.
cseFindExpr :: Expr -> CSEEnv -> Maybe CSEVal
cseFindExpr expr env = lookup expr $ available env

-- | Find a CSE expression corresponding to the given variable's value.
cseGetValue :: Var -> CSEEnv -> Maybe Expr
cseGetValue v env = IntMap.lookup (fromIdent $ varID v) $ valuation env

-- | Produce the expression corresponding to a value.
interpretVal :: CSEEnv -> Val -> Maybe Expr
interpretVal env value =
  case value
  of VarV v -> Just $ simplify env $ VarExpr v
     LitV l -> Just (LitExpr l)
     _      -> Nothing

-- | Produce the expression corresponding to a primitive operation.
interpretPrim :: CSEEnv -> Prim -> [Expr] -> Maybe Expr
interpretPrim env op args = fmap (simplify env) $
  case op
  of PrimAddZ sgn sz -> Just $ ca (AddZOp sgn sz)
     PrimSubZ sgn sz -> Just $ subtract_op sgn sz
     PrimModZ sgn sz -> Just $ binary (ModZOp sgn sz)
     PrimAddP        -> Just $ binary AddPOp
     -- Only constant loads can become expressions
     PrimLoad Constant ty -> Just $ load_op ty
     _               -> Nothing
  where
    -- Print a debug message
    debug Nothing = Nothing
    debug (Just e) = traceShow msg $ Just e 
      where
        msg = pprPrim op <+> hsep (map (parens . pprExpr) args) $$ pprExpr e

    ca caop =
      case args
      of [a1, a2] -> CAExpr caop [a1, a2]
         _ -> internalError "interpretPrim"

    binary binop =
      case args
      of [a1, a2] -> BinExpr binop a1 a2
         _ -> internalError "interpretPrim"
         
    unary unop =
      case args
      of [a] -> UnExpr unop a
         _ -> internalError "interpretPrim"

    subtract_op sgn sz =
      case args
      of [a1, a2] ->
           let negated = simplify' $ UnExpr (NegateZOp sgn sz) a2
           in CAExpr (AddZOp sgn sz) [a1, negated]

    load_op ty =
      case args
      of [base, off] ->
           let pointer = simplify' $ BinExpr AddPOp base off
           in UnExpr (LoadOp ty) pointer

-- | Update the environment to reflect the state of memory after a
--   store of constant memory executes.
interpretStore :: CSEEnv -> ValueType -> Expr -> Expr -> Expr -> Maybe CSEEnv
interpretStore env ty base off val =
  case cseFindExpr val env `mplus` exprToCSEVal val
  of Just cse_val ->
       let pointer = simplify env $ BinExpr AddPOp base off
           load_op = UnExpr (LoadOp ty) pointer
           env' = env {available = insert load_op cse_val $ available env}
       in Just env'
     Nothing -> Nothing

-- | Return True if the expression can be converted to a value.
--   The expression should be a simplified expression.
isZeroAtomExpr :: Expr -> Bool
isZeroAtomExpr expr = 
  case expr
  of VarExpr _ -> True 
     LitExpr _ -> True
     _ -> False

-- | Return True if the expression can be converted to a value or a single
--   atom.
--   The expression should be a simplified expression.
isOneAtomExpr :: Expr -> Bool
isOneAtomExpr expr =
  case expr
  of VarExpr _ -> True 
     LitExpr _ -> True
     CAExpr _ [e1, e2] -> isZeroAtomExpr e1 && isZeroAtomExpr e2
     CAExpr _ _        -> False
     BinExpr _ e1 e2   -> isZeroAtomExpr e1 && isZeroAtomExpr e2
     BinExpr _ _ _     -> False
     UnExpr (LoadOp _) _ ->
       case unpackLoadExpr expr
       of Just (_, base, offset) -> isZeroAtomExpr base
     UnExpr _ arg -> isZeroAtomExpr arg

generateExprAtom :: forall m. Supplies m (Ident Var) => Expr -> Gen m Atom
generateExprAtom expression = 
  case expression
  of VarExpr _ -> value_atom
     LitExpr _ -> value_atom
     CAExpr _ [] -> internalError "generateExprAtom"
     CAExpr op (arg:args) -> do acc <- generateExprAtom arg
                                ca (ca_op op) acc args
  where
    value_atom = do v <- generateExprVal expression
                    return (ValA [v])

    ca_op (AddZOp sgn sz) = PrimAddZ sgn sz

    ca op acc args = foldM accumulate acc args
      where
        [rt] = primReturnType op
        accumulate acc arg = do
          acc_val <- emitAtom1 rt acc
          val <- generateExprVal arg
          return $ PrimA op [acc_val, val]

generateExprVal :: Supplies m (Ident Var) => Expr -> Gen m Val
generateExprVal expression =
  case expression
  of VarExpr v -> return (VarV v)
     LitExpr l -> return (LitV l)
     _ -> emitAtom1 (exprType expression) =<< generateExprAtom expression

{-
-- | Generate the code of an expression.
generateExprCode :: Supplies m (Ident Var) => Expr -> Gen m Val
generateExprCode expression =
  case expression
  of VarExpr v -> return (VarV v)
     LitExpr l -> return (LitV l)
     CAExpr (AddZOp sgn sz) es ->
       generateSum sgn sz es

     BinExpr op e1 e2 -> do
       v1 <- generateExprCode e1
       v2 <- generateExprCode e2
       let prim =
             case op
             of ModZOp sgn sz -> PrimModZ sgn sz
                AddPOp        -> PrimAddP
           rt = case primReturnType prim
                of [t] -> t
                   _ -> internalError "generateExprCode"
       emitAtom1 rt (PrimA prim [v1, v2])

     UnExpr (NegateOp sgn sz) e -> do
       v <- generateExprCode e
       let rt = PrimType $ IntType sgn sz
       emitAtom1 rt (PrimA (PrimSubZ sgn sz) [LitV (IntL sgn sz 0), v])

     UnExpr (LoadOp ty) (BinExpr AddPOp base offset) -> do
       base_val <- generateExprCode base
       offset_val <- generateExprCode offset
       emitAtom1 ty (PrimA (PrimLoad ty) [base_val, offset_val])

     UnExpr (LoadOp ty) e -> do
       v <- generateExprCode e
       emitAtom1 ty (PrimA (PrimLoad ty) [v, nativeIntV 0])

generateSum sgn sz [] = return $ LitV (IntL sgn sz 0)
generateSum sgn sz [e] = generateExprCode e
generateSum sgn sz es =
  -- Get the terms that are added and the terms that are subtracted 
  let (positives, negatives) = List.partition is_negated es
      subtracted = [e | UnExpr (NegateOp _ _) e <- negatives]
      (first_expr, positives') =
        case positives
        of []   -> (LitExpr (IntL sgn sz 0), [])
           e:es -> (e, es)
  in do first_val <- generateExprCode first_expr
        partial_sum <- foldM generate_and_add first_val positives'
        foldM generate_and_sub partial_sum negatives
  where
    is_negated (UnExpr (NegateOp _ _) _) = True
    is_negated _ = False

    generate_and_add acc expr =
      primAddZ (PrimType $ IntType sgn sz) acc =<< generateExprCode expr
    
    generate_and_sub acc expr =
      primSubZ (PrimType $ IntType sgn sz) acc =<< generateExprCode expr
-}
-------------------------------------------------------------------------------
-- Expression simplification

-- | Convert an expression to a semi-canonical form and check whether the
--   expression is already in the environment.  If the expression can be
--   simplified to a literal or it is already in the environment, then  
--   a 'Simplified' term is returned.  Otherwise a 'Translated' term is
--   returned.
simplify :: CSEEnv -> Expr -> Expr
simplify env expression = 
  case expression
  of VarExpr v        -> fromMaybe expression $ cseGetValue v env
     _                -> simplify' expression

simplify' expression =
  case expression
  of VarExpr v        -> expression
     LitExpr _        -> expression
     CAExpr op es     -> simplifyCA op es
     BinExpr op e1 e2 -> simplifyBinary op e1 e2
     UnExpr op e      -> simplifyUnary op e

simplifyCA op es = zusSum op $ partialEvalSum $ flatten op es

flatten op es = go es 
  where
    go (e:es) =
      case e
      of CAExpr op' es' | op == op' -> es' ++ go es
         _ -> e : go es
    go [] = []

partialEvalSum es = peval 0 id es
  where
    peval acc hd (LitExpr (IntL _ _ n) : es) = peval (acc + n) hd es
    peval acc hd (e : es) = peval acc (hd . (e:)) es
    peval acc hd [] = (acc, hd [])

zusSum op@(AddZOp sgn sz) values = 
  case values
  of (0, [e]) -> e
     (n, [])  -> LitExpr (IntL sgn sz n)
     (0, es)  -> CAExpr op es
     (n, es)  -> CAExpr op (LitExpr (IntL sgn sz n) : es)

simplifyBinary op@(ModZOp sgn sz) larg rarg
  -- Evaluate if both operands are known, or if one operand is an identity
  | isIntLitExpr 0 larg = larg
  | isIntLitExpr 1 rarg = LitExpr (IntL sgn sz 0)
  | LitExpr (IntL _ _ lnum) <- larg,
    LitExpr (IntL _ _ rnum) <- rarg =
      LitExpr (IntL sgn sz (lnum `mod` rnum))
  | otherwise = BinExpr op larg rarg

simplifyBinary AddPOp larg rarg
  | isIntLitExpr 0 rarg = larg
  | BinExpr AddPOp larg' larg2 <- larg =
      let rarg' = simplify' $
                  CAExpr (AddZOp Signed nativeIntSize) [larg2, rarg]
      in simplifyBinary AddPOp larg' rarg'
  | otherwise = BinExpr AddPOp larg rarg

simplifyUnary op arg =
  case op
  of NegateZOp sgn sz ->
       case arg
       of CAExpr sub_op@(AddZOp _ _) args -> CAExpr sub_op (map negateE args)
          LitExpr (IntL _ _ n) -> LitExpr $ IntL sgn sz (negate n)
          _ -> UnExpr op arg
     LoadOp ty ->
       UnExpr op arg
  where
    -- Double negation cancels
    negateE (UnExpr (NegateZOp _ _) arg) = arg
    negateE e                            = UnExpr op e

       {-
  case runWriter $ canonicalize env expression
  of (e, Any True)  -> Simplified e
     (e, Any False) -> Translated e-}

{-
-- | Indicate that something was changed during simplification, making the
--   simplified term preferable to the original.
somethingChanged :: Writer Any ()
somethingChanged = tell (Any True)

canonicalize env expression =
  case expression
  of VarExpr _ -> case lookup expression env
                  of Just expr' -> return expr'
                     Nothing    -> return expression
     LitExpr _ -> return expression
     CAExpr op@(AddZOp sgn sz) es ->
       zusSum sgn sz =<< partialEvalSum (flattenSum es)
     BinExpr _ _ _ -> return expression
     UnExpr _ _ -> return expression

flattenSum (e:es) =
  case e
  of CAExpr (AddZOp _ _) es' -> es' ++ flattenSum es
     _ -> e : flattenSum es

flattenSum [] = []

-- Apply zero, unit, and singleton rules
zusSum :: Signedness -> Size -> (Maybe Integer, [Expr]) -> Writer Any Expr
zusSum sgn sz values =
  case values
  of (Nothing, [e]) -> somethingChanged >> return e -- Singleton
     (Just 0,  es ) -> somethingChanged >> zusSum sgn sz (Nothing, es) -- Unit
     (Just n,  es ) -> return $ CAExpr op (LitExpr (IntL sgn sz n) : es)
     (Nothing, es ) -> return $ CAExpr op es
  where
    op = AddZOp sgn sz

partialEvalSum :: [Expr] -> Writer Any (Maybe Integer, [Expr])
partialEvalSum es = peval Nothing id es
  where
    peval lit_acc var_acc es =
      case es
      of LitExpr (IntL _ _ n) : es' ->
           case lit_acc
           of Nothing -> peval (Just n) var_acc es'
              Just m -> do
                somethingChanged
                peval (Just (m + n)) var_acc es'
         e : es' -> peval lit_acc (var_acc . (e:)) es'
         [] -> return (lit_acc, var_acc [])
-}