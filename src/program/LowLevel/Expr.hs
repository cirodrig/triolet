{-| Expressions representing side-effect-free computations.
These expressions are used in common subexpression elimination.
-}

{-# LANGUAGE TypeFamilies, FlexibleContexts, Rank2Types #-}
module LowLevel.Expr
       (Expr,
        CSEEnv,
        emptyCSEEnv,
        Interpretation(..),
        interpretVal,
        interpretPrim,
        updateCSEEnv,
        generateExprCode
       )
where

import Prelude hiding(lookup)

import Control.Monad
import qualified Data.Map as Map
import Data.Maybe

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Supply
import LowLevel.Build
import LowLevel.Types
import LowLevel.Syntax

-- | A binary operator.
data BinOp =
    AddZOp !Signedness !Size
  | SubZOp !Signedness !Size
  | ModZOp !Signedness !Size
  | AddPOp
    deriving(Eq, Ord)

-- | A unary operator.
data UnOp =
    LoadOp !ValueType
    deriving(Eq, Ord)

-- | A pure expression.   
data Expr =
    VarExpr !Var
  | LitExpr !Lit
  | BinExpr !BinOp Expr Expr
  | UnExpr !UnOp Expr

-- | A lookup trie for matching expressions.
--
-- There is one field for each 'Expr' constructor.
data TrieNode v =
  TrieNode
  { tVar :: Map.Map Var v
  , tLit :: Map.Map Lit v
  , tBin :: Map.Map BinOp (TrieNode (TrieNode v))
  , tUn  :: Map.Map UnOp (TrieNode v)
  }

class Trie t where
  type Key t
  empty :: t v
  alter :: (Maybe v -> Maybe v) -> Key t -> t v -> t v
  insert :: Key t -> v -> t v -> t v
  insert k v = alter (const (Just v)) k
  lookup :: Key t -> t v -> Maybe v

alterSub :: (Trie t, Trie t') =>
            Key t' -> (t v -> t v) -> t' (t v) -> t' (t v)
alterSub k f = alter (Just . f . fromMaybe empty) k

instance Ord k => Trie (Map.Map k) where
  type Key (Map.Map k) = k
  empty = Map.empty
  alter = Map.alter
  insert = Map.insert
  lookup = Map.lookup

instance Trie TrieNode where
  type Key TrieNode = Expr
  empty = 
    TrieNode
    { tVar = empty
    , tLit = empty
    , tBin = empty
    , tUn = empty
    }
  alter f k tr = updateTrieNode (alter f) k tr
  insert k v tr = updateTrieNode (\k -> insert k v) k tr
  lookup k tr =
    case k
    of VarExpr var -> lookup var $ tVar tr
       LitExpr lit -> lookup lit $ tLit tr
       BinExpr op e1 e2 -> lookup3 op e1 e2 $ tBin tr
       UnExpr op e -> lookup2 op e $ tUn tr
    where
      lookup2 k1 k2 = lookup k2 <=< lookup k1
      lookup3 k1 k2 k3 = lookup k3 <=< lookup k2 <=< lookup k1

updateTrieNode :: (forall t'. Trie t' => Key t' -> t' v -> t' v) -> Expr
               -> TrieNode v -> TrieNode v
updateTrieNode f k tr =
  case k
  of VarExpr var -> tr {tVar = f var $ tVar tr}
     LitExpr lit -> tr {tLit = f lit $ tLit tr}
     BinExpr op e1 e2 -> tr {tBin = alter3 op e1 e2 $ tBin tr}
     UnExpr op e -> tr {tUn = alter2 op e $ tUn tr}
  where
    alter3 k1 k2 k3 = alterSub k1 $ alterSub k2 $ f k3
    alter2 k1 k2 = alterSub k1 $ f k2

-------------------------------------------------------------------------------

-- | A CSE environment maps expressions to simpler expressions, usually values.
type CSEEnv = TrieNode Expr

emptyCSEEnv :: CSEEnv
emptyCSEEnv = empty

data Interpretation =
    -- | Cannot be represented as an expression
    NoInterpretation
    -- | Can be represented as an expression, but not worth replacing the
    --   original code
  | Translated { interpretation :: Expr}
    -- | Transformed to a simpler expression
  | Simplified { interpretation :: Expr}

-- | Produce the expression corresponding to a value.
interpretVal :: CSEEnv -> Val -> Interpretation
interpretVal env value =
  case value
  of VarV v -> let var_expr = VarExpr v
               in maybe (Translated var_expr) Simplified $ lookup var_expr env
     LitV l -> Translated (LitExpr l)
     _      -> NoInterpretation

-- | Produce the expression corresponding to a primitive operation.
interpretPrim :: CSEEnv -> Prim -> [Expr] -> Interpretation
interpretPrim env op args = canonicalizeExpr env $
  case op
  of PrimAddZ sgn sz -> binary (AddZOp sgn sz)
     PrimSubZ sgn sz -> binary (SubZOp sgn sz)
     PrimModZ sgn sz -> binary (ModZOp sgn sz)
     PrimAddP        -> binary AddPOp
     PrimLoad ty     -> unary (LoadOp ty)
  where
    binary binop =
      case args
      of [a1, a2] -> BinExpr binop a1 a2
         _ -> internalError "interpretPrim"
    unary unop =
      case args
      of [a] -> UnExpr unop a
         _ -> internalError "interpretPrim"

updateCSEEnv :: Val -> Interpretation -> CSEEnv -> CSEEnv
updateCSEEnv val interpretation env =
  case val
  of VarV v -> case interpretation 
               of NoInterpretation -> env
                  Translated i     -> insert (VarExpr v) i env
                  Simplified i     -> insert (VarExpr v) i env
     _ -> env

-- | Convert an expression to a semi-canonical form and check whether the
--   expression is already in the environment.  If the expression can be
--   simplified to a literal or it is already in the environment, then  
--   a 'Simplified' term is returned.  Otherwise a 'Translated' term is
--   returned.
canonicalizeExpr :: CSEEnv -> Expr -> Interpretation
canonicalizeExpr env expression =
  case expression
  of BinExpr (AddZOp sgn sz) e1 e2 -> undefined

-- | Generate the code of an expression.
generateExprCode :: Supplies m (Ident Var) => Expr -> Gen m Val
generateExprCode expression =
  case expression
  of VarExpr v -> return (VarV v)
     LitExpr l -> return (LitV l)
     BinExpr op e1 e2 -> do
       v1 <- generateExprCode e1
       v2 <- generateExprCode e2
       let prim =
             case op
             of AddZOp sgn sz -> PrimAddZ sgn sz
                SubZOp sgn sz -> PrimSubZ sgn sz
                ModZOp sgn sz -> PrimModZ sgn sz
                AddPOp        -> PrimAddP
           rt = case primReturnType prim
                of [t] -> t
                   _ -> internalError "generateExprCode"
       emitAtom1 rt (PrimA prim [v1, v2])

     UnExpr (LoadOp ty) (BinExpr AddPOp base offset) -> do
       base_val <- generateExprCode base
       offset_val <- generateExprCode offset
       emitAtom1 ty (PrimA (PrimLoad ty) [base_val, offset_val])

     UnExpr (LoadOp ty) e -> do
       v <- generateExprCode e
       emitAtom1 ty (PrimA (PrimLoad ty) [v, nativeIntV 0])

