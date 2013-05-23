{-| Dead code elimination.

This module performs single-pass dead code elimination.
Variables that are not used, and are produced by a non-side-effecting 
atom, are eliminated.

Let-expressions of the form @let x = A in x@ are simplified to remove
the temporary variables.  This transformation is especially important
when the atom @A@ is a function call, because it turns a non-tail call
into a tail call.
-}

{-# LANGUAGE Rank2Types #-}
module LowLevel.DeadCode(eliminateDeadCode)
where

import Prelude hiding(mapM, sequence)
import Control.Applicative
import qualified Data.Graph as Graph
import qualified Data.IntMap as IntMap
import Data.Monoid
import Data.Traversable

import Common.Error
import Common.Identifier
import LowLevel.Syntax
import LowLevel.Print
import LowLevel.CodeTypes

-- | A map from variable IDs to the number of uses the variable has.
--   If a variable has no uses, it is not in the map.
type UseMap = IntMap.IntMap Uses

v `isUsedIn` m = fromIdent (varID v) `IntMap.member` m

lookupUses v m = case IntMap.lookup (fromIdent (varID v)) m
                 of Nothing -> ZeroUses
                    Just x  -> x

deleteUse v m = IntMap.delete (fromIdent (varID v)) m

deleteUses vs m = foldr deleteUse m vs

useUnion = IntMap.unionWith mappend

useUnions = IntMap.unionsWith mappend

-- | Estimate the size of the code required to define a function,
--   not including the function body.  The size depends on the number of
--   function parameters and returns.
--
--   When computing code size, this component is not accounted to the 
--   function itself, but to the place where the function is defined.
--   It's done this way because this code is not generated for inlined
--   instances of the function.
funDefinitionSize :: Fun -> Int
funDefinitionSize f = length (funParams f) + length (funReturnTypes f) + 1 

-- | A map giving the arities of functions
type ArityMap = IntMap.IntMap Int

-- | The DCE monad.
newtype DCEM a = DCEM (ArityMap -> DCEResult a)

data DCEResult a =
  DCEResult
  { size      :: {-#UNPACK#-}!Int
  , uses      :: UseMap
  , dceResult :: a
  }

type DCE a = a -> DCEM a

instance Functor DCEM where
  fmap f (DCEM x) = DCEM $ \arity ->
    case x arity 
    of DCEResult s u y -> DCEResult s u (f y)

modifyResult :: (DCEResult a -> DCEResult b) -> DCEM a -> DCEM b
modifyResult f (DCEM x) = DCEM $ \arity -> f $ x arity

instance Applicative DCEM where
  pure x  = DCEM $ \_ -> DCEResult 0 IntMap.empty x
  DCEM f1 <*> DCEM f2 =
    DCEM $ \arity ->
    case f1 arity
    of DCEResult s1 u1 f ->
         case f2 arity
         of DCEResult s2 u2 x ->
              DCEResult (s1 + s2) (useUnion u1 u2) (f x)

instance Monad DCEM where
  return = pure
  DCEM f >>= k = DCEM $ \arity ->
    case f arity
    of DCEResult s1 u1 x ->
         case k x
         of DCEM f' ->
              case f' arity 
              of DCEResult s2 u2 y ->
                   DCEResult (s1 + s2) (useUnion u1 u2) y

-- | Add something to the code size
nudge :: Int -> DCEM a -> DCEM a
nudge n m = modifyResult (\x -> x {size = size x + n}) m

use :: Var -> DCEM ()
use v = DCEM $ \arity ->
  let use_map = IntMap.singleton (fromIdent $ varID v) OneUse
  in DCEResult 0 use_map ()

-- | Add the arity of a defined function to the environment
assumeFunctionArity :: Var -> Int -> DCEM a -> DCEM a
assumeFunctionArity fname n (DCEM g) = DCEM $ \arity ->
  let arity' = IntMap.insert (fromIdent $ varID fname) n arity
  in g arity'

assumeFunctionArities :: [FunDef] -> DCEM a -> DCEM a
assumeFunctionArities defs m = foldr assume_arity m defs
  where
    assume_arity (Def v f) m = assumeFunctionArity v (length $ funParams f) m

-- | Try to get the arity of a function, given its name
lookupFunctionArity :: Var -> DCEM (Maybe Int)
lookupFunctionArity v = DCEM $ \arity ->
  DCEResult 0 IntMap.empty (IntMap.lookup (fromIdent $ varID v) arity)

-- | Get the code size computed by the computation
tellSize :: DCEM a -> DCEM (Int, a)
tellSize = modifyResult $ \(DCEResult s u x) -> DCEResult s u (s, x)

-- | Get the uses computed by the computation
tellUses :: DCEM a -> DCEM (UseMap, a)
tellUses = modifyResult $ \(DCEResult s u x) -> DCEResult s u (u, x)

-- | Get all observed uses.  Don't propagate uses.
takeUses :: DCEM a -> DCEM (UseMap, a)
takeUses =
  modifyResult $ \(DCEResult s u x) -> DCEResult s IntMap.empty (u, x)

putUses :: UseMap -> DCEM ()
putUses uses = DCEM $ \_ -> DCEResult 0 uses ()

dceVal :: DCE Val
dceVal value = nudge 1 $
  case value
  of VarV v -> use v *> pure value
     RecV rec vals -> RecV rec <$> dceVals vals
     LitV l -> pure value

dceVals :: DCE [Val]
dceVals vs = traverse dceVal vs

-- | Return True if the atom can have an observable side effect in normal
--   program execution, other than producing a result value.
atomHasSideEffect :: Atom -> DCEM Bool
atomHasSideEffect atom = 
  case atom
  of ValA {} -> return False

     -- Partially applied functions don't have side effects.
     -- If this is a closure call with a known callee, check whether it's
     -- partially applied.
     CallA ClosureCall (VarV callee) args -> do
       arity <- lookupFunctionArity callee
       case arity of
         Just n | n > length args -> return False -- Partial application
         _ -> return True       -- Fully applied or unknown callee

     CallA {} -> return True
     PrimA prim _ -> return $ primHasSideEffect prim
     PackA {} -> return False
     UnpackA {} -> return False
     
-- | Return True if an execution of this primitive operation can have an
--   observable side effect in normal program execution, other than 
--   producing a result value or an arithmetic exception.
--
--   Loads have no side effect.  They have no observable effect and don't 
--   fail in normal execution.
primHasSideEffect :: Prim -> Bool
primHasSideEffect prim =
  case prim
  of PrimCastZ {}         -> False
     PrimExtendZ {}       -> False
     PrimAddZ {}          -> False
     PrimSubZ {}          -> False
     PrimMulZ {}          -> False
     PrimModZ {}          -> False
     PrimDivZ {}          -> False
     PrimMaxZ {}          -> False
     PrimMinZ {}          -> False
     PrimAndZ {}          -> False
     PrimOrZ {}           -> False
     PrimXorZ {}          -> False
     PrimComplZ {}        -> False
     PrimShiftL {}        -> False
     PrimShiftR {}        -> False
     PrimCmpZ {}          -> False
     PrimCmpP {}          -> False
     PrimSelect {}        -> False
     PrimAnd {}           -> False
     PrimOr {}            -> False
     PrimNot {}           -> False
     PrimAddP {}          -> False
     PrimSubP {}          -> False
     PrimLoad {}          -> False
     PrimStore {}         -> True
     PrimAAddZ {}         -> True
     PrimCastToOwned {}   -> False
     PrimCastFromOwned {} -> False
     PrimCastFromCursor {} -> False
     PrimCursorBase {}    -> False
     PrimCastPtrToInt {}  -> False
     PrimGetFrameP {}     -> False
     PrimCastZToF {}      -> False
     PrimCastFToZ {}      -> False
     PrimCmpF {}          -> False
     PrimAddF {}          -> False
     PrimSubF {}          -> False
     PrimMulF {}          -> False
     PrimModF {}          -> False
     PrimDivF {}          -> False
     PrimRoundF {}        -> False
     PrimPowF {}          -> False
     PrimUnaryF {}        -> False

dceAtom :: DCE Atom
dceAtom atom = nudge 1 $
  case atom
  of ValA vs -> ValA <$> dceVals vs
     CallA conv v vs -> CallA conv <$> dceVal v <*> dceVals vs
     PrimA prim vs -> PrimA prim <$> dceVals vs 
     PackA rec vs -> PackA rec <$> dceVals vs
     UnpackA rec v -> UnpackA rec <$> dceVal v

-- | Perform dead code elimination on a statement.
-- 
--   Let and letrec expressions may be removed.
dceStm :: DCE Stm
dceStm statement =
  case statement
  of LetE params rhs body ->
       dceLet params rhs body
     LetrecE defs body ->
       dceLetrec defs body
     SwitchE scrutinee alts ->
       nudge 1 $ SwitchE <$> dceVal scrutinee <*> traverse dceAlt alts
     ReturnE atom ->
       ReturnE <$> dceAtom atom
     ThrowE val ->
       ThrowE <$> dceVal val
  where
    dceAlt (x, stm) = (,) x <$> dceStm stm

dceLet params rhs body = do
  -- Analyze the body.  Remove local variables from the use set.
  (uses, body') <- takeUses $ dceStm body
  putUses $ deleteUses params uses
  
  -- Eliminate the let expression if its result is dead and it is not used
  has_effect <- atomHasSideEffect rhs
  if has_effect || any (`isUsedIn` uses) params
    then do rhs' <- dceAtom rhs
            return $ rebuildLet params rhs' body'
    else return body'

-- | Construct a let expression.
--
--   If the expression has the form @let x = A in x@, then eliminate the 
--   variable binding and construct a return expression instead.
--
--   This also works if the expression has the form @let x = A in V@ for
--   any value @V@, if @x@ and @V@ have unit type.

rebuildLet params rhs body
  | ReturnE (ValA vals) <- body, match_params params vals =
      ReturnE rhs
  | otherwise = LetE params rhs body
  where
    match_params (p:params) (v:vals) =
      match_param p v && match_params params vals
    
    match_params [] [] = True
    
    match_params _ _ = False

    -- Match is successful if the return value is just the parameter,
    -- or if both things have unit type
    match_param p (VarV v) | p == v = True
    match_param p v        | varType p == PrimType UnitType &&
                             valType v == PrimType UnitType = True
    match_param _ _        = False

dceLetrec defs body = make_letrec <$> dceLocalDefGroup defs (dceStm body)
  where
    make_letrec (defs', body') = foldr LetrecE body' defs'

dceLocalDefGroup :: Group FunDef -> DCEM a -> DCEM ([Group FunDef], a)
dceLocalDefGroup defs body = do
  (groups, use_map, body') <-
    dceDefGroup assume_function definiendum dce_def defs body
    
  -- Annotate functions that are used once.  They will be inlined.
  let ann_groups = map (fmap (setFunDefUses use_map)) groups
  return (ann_groups, body')
  where
    assume_function :: FunDef -> DCEM b -> DCEM b
    assume_function fdef = assumeFunctionArities [fdef]
    dce_def (Def v f) = Def v <$> dceFun f

-- | Rebuild a function definition after DCE.
setFunDefUses :: UseMap -> FunDef -> FunDef 
setFunDefUses use_map (Def fname f) =
  let fuses = lookupUses fname use_map
      annotated_fun = setFunUses fuses f
  in Def fname $! annotated_fun

-- | Perform dead code elimination on a function.  Only the function body 
--   contributes to the code size.  Use information is cleared. 
--   (Use information is annotated when processing the definition group
--   containing the function).
dceFun :: DCE Fun
dceFun fun = do
  (body_size, body) <- tellSize $ dceStm (funBody fun)
  let fun' = fun { funSize = codeSize body_size
                 , funUses = ManyUses
                 , funBody = body}
  return fun'

-- | Perform dead code elimination on a data definition.  The data definition
--   is scanned to find out what variables it references.
dceDataDef :: DCE DataDef
dceDataDef (Def v (StaticData val)) =
  (Def v . StaticData) <$> dceVal val

dceTopLevelDef :: DCE GlobalDef
dceTopLevelDef (GlobalFunDef (Def v f)) = GlobalFunDef . Def v <$> dceFun f
dceTopLevelDef (GlobalDataDef ddef) = GlobalDataDef <$> dceDataDef ddef

dceDefGroup :: (forall b. a -> DCEM b -> DCEM b) -> (a -> Var) -> DCE a
            -> Group a -> DCEM b -> DCEM ([Group a], UseMap, b)
dceDefGroup assume get_definiendum dce group m = do
  -- Find out which group members are used
  (body_uses, new_body) <- assume_defs $ takeUses m

  case group of
    NonRec def 
      | not $ get_definiendum def `isUsedIn` body_uses ->
          -- This function is not used, we don't need to scan it
          putUses body_uses >> return ([], body_uses, new_body)
      | otherwise -> do
          def' <- dce def
          putUses body_uses >> return ([NonRec def'], body_uses, new_body)
    Rec defs -> do
      -- Split this group into minimal mutually recursive groups.
      -- First, find uses in each function.
      uses_and_defs <- assume_defs $ mapM (takeUses . dce) defs

      -- Partition this definition group
      let annotated_uses =
            [(varID $ get_definiendum def, uses, def)
            | (uses, def) <- uses_and_defs]
          (partitioned_uses, groups) =
            partitionDefGroup annotated_uses body_uses
      putUses partitioned_uses
      return (groups, partitioned_uses, new_body)
  where
    assume_defs :: DCEM c -> DCEM c
    assume_defs m = foldr assume m $ groupMembers group

dceTopLevelDefGroup :: Group GlobalDef
                    -> DCEM a
                    -> DCEM ([Group GlobalDef], a)
dceTopLevelDefGroup group m = do
  (groups, use_map, x) <-
    dceDefGroup assume_function globalDefiniendum dceTopLevelDef group m

  -- Annotate functions that are used once.  They will be inlined.
  let ann_groups = map (fmap (annotate_uses use_map)) groups

  return (groups, x)
  where
    assume_function :: GlobalDef -> DCEM a -> DCEM a
    assume_function (GlobalFunDef fdef) = assumeFunctionArities [fdef]
    assume_function (GlobalDataDef _) = id
    
    annotate_uses use_map (GlobalFunDef fdef) =
      GlobalFunDef $ setFunDefUses use_map fdef
    
    annotate_uses _ ddef@(GlobalDataDef _) = ddef

dceTopLevelDefGroups (group : groups) m = do
  (groups1, (groups2, x)) <-
    dceTopLevelDefGroup group $ dceTopLevelDefGroups groups m
  return (groups1 ++ groups2, x)
  
dceTopLevelDefGroups [] m = do
  x <- m
  return ([], x)

-- | Partition a definition group into SCCs.
partitionDefGroup :: forall a.
                     [(Ident Var, UseMap, a)]
                  -> UseMap
                  -> (UseMap, [Group a])
partitionDefGroup members external_refs =
  let member_id_set =
        IntMap.fromList [(fromIdent n, ManyUses) | (n, _, _) <- members]
      
      -- Restrict set 's' to the members of the definition group
      restrict s = IntMap.intersection s member_id_set

      -- Create a dummy variable ID for the graph node that represents 
      -- external references to the definition group
      dummy_id = toIdent $ 1 + fst (IntMap.findMax member_id_set)

      graph = (Nothing, dummy_id, nodes $ restrict external_refs) :
              [(Just (x, ys), n, nodes $ restrict ys) | (n, ys, x) <- members]
      
      -- Partition into SCCs.
      -- Only keep the definitions that precede the dummy node
      -- (meaning that they're referenced by something external).
      -- The remaining definitions are dead.
      sccs = fst $ break is_dummy_node $ Graph.stronglyConnComp graph
      
      defgroups = to_defgroups sccs
      uses = useUnion (to_usemap sccs) external_refs
  in (uses, defgroups)
  where
    nodes :: UseMap -> [Ident Var]
    nodes = map toIdent . IntMap.keys

    to_usemap sccs = useUnions $ concatMap members sccs
      where
        members :: Graph.SCC (Maybe (a, UseMap)) -> [UseMap]
        members (Graph.AcyclicSCC (Just (_, uses))) = [uses]
        members (Graph.AcyclicSCC _) = internalError "partitionDefGroup"
        members (Graph.CyclicSCC xs) =
          case sequence xs
          of Just xs' -> map snd xs'
             _ -> internalError "partitionDefGroup"

    to_defgroups sccs = map to_defgroup sccs

    to_defgroup (Graph.AcyclicSCC (Just x)) =
      NonRec (fst x)
    to_defgroup (Graph.AcyclicSCC _) =
      internalError "partitionDefGroup"
    to_defgroup (Graph.CyclicSCC xs) =
      case sequence xs
      of Just xs' -> Rec (map fst xs')
         _ -> internalError "partitionDefGroup"
    
    is_dummy_node (Graph.AcyclicSCC Nothing) = True
    is_dummy_node _ = False

assumeImportedArity impent m =
  case impent
  of ImportClosureFun ep _ ->
       assumeFunctionArity (importVar impent) (functionArity ep) m
     ImportPrimFun _ ty _ ->
       assumeFunctionArity (importVar impent) (length $ ftParamTypes ty) m
     ImportData _ _ -> m

assumeImportedArities imps m = foldr assumeImportedArity m imps

dceTopLevel :: [Import]          -- ^ Imported variables
            -> [Group GlobalDef] -- ^ Global definitions
            -> [Var]             -- ^ Exported variables
            -> DCEM [Group GlobalDef]
dceTopLevel imps defs exports = assumeImportedArities imps $ do
  -- Perform DCE and find all uses
  (new_defs, ()) <- dceTopLevelDefGroups defs use_exports
  return new_defs
  where
    -- All exported variables are used an unknown number of times
    use_exports = 
      putUses $ IntMap.fromList [(fromIdent $ varID v, ManyUses)
                                | v <- exports]

-- | Eliminate dead code in a module.
--
--   Also annotate functions with code size and number of uses.
eliminateDeadCode :: Module -> Module
eliminateDeadCode mod@(Module { moduleGlobals = gs
                              , moduleExports = es
                              , moduleImports = imps}) =
  let gs' = runDCE $ dceTopLevel imps gs (map fst es)
  in mod {moduleGlobals = gs'}
  where
    runDCE (DCEM f) =
      dceResult $ f IntMap.empty