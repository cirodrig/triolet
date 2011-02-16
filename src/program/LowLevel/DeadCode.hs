
module LowLevel.DeadCode(eliminateDeadCode)
where

import Prelude hiding(mapM)
import Control.Applicative
import qualified Data.IntMap as IntMap
import Data.Monoid
import Data.Traversable

import Common.Identifier
import LowLevel.Syntax
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
     LamV f -> LamV <$> nudge (funDefinitionSize f) (dceFun f)

dceVals :: DCE [Val]
dceVals vs = traverse dceVal vs

-- | Return True if the atom can have an observable side effect in normal
--   program execution, other than producing a result value.
atomHasSideEffect :: Atom -> DCEM Bool
atomHasSideEffect atom = 
  case atom
  of ValA {} -> return False
     CallA _ (VarV callee) args -> do
       arity <- lookupFunctionArity callee
       case arity of
         Just n | n > length args -> return False -- Partial application
         _ -> return True       -- Fully applied or unknown callee
     CallA {} -> return True    -- Unknown callee
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
     PrimCmpZ {}          -> False
     PrimCmpP {}          -> False
     PrimAnd {}           -> False
     PrimOr {}            -> False
     PrimNot {}           -> False
     PrimAddP {}          -> False
     PrimLoad {}          -> False
     PrimStore {}         -> True
     PrimAAddZ {}         -> True
     PrimCastToOwned {}   -> False
     PrimCastFromOwned {} -> False
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
  where
    dceAlt (x, stm) = (,) x <$> dceStm stm

dceLet params rhs body = do
  (uses, body') <- takeUses $ dceStm body
  putUses $ deleteUses params uses
  has_effect <- atomHasSideEffect rhs 
  if has_effect || any (`isUsedIn` uses) params
    then do rhs' <- dceAtom rhs
            return (LetE params rhs' body')
    else return body'

dceLetrec defs body = make_letrec <$> dceDefGroup defs (dceStm body)
  where
    make_letrec (defs', body') 
      | null defs' = body'
      | otherwise = LetrecE defs' body'

dceDefGroup :: [FunDef] -> DCEM a -> DCEM ([FunDef], a)
dceDefGroup defs body = assumeFunctionArities defs $ do
  (body_uses, new_body) <- takeUses body

  -- Perform DCE and collect use information in function bodies
  annotated_defs <- forM defs $ \(Def v f) -> takeUses $ do
    f' <- dceFun f
    return (Def v f')
    
  let all_uses = useUnions (body_uses : map fst annotated_defs)

  -- Remove unused functions
  -- TODO: use reachability from body as liveness criterion
  let live_defs = filter is_live annotated_defs
        where
          is_live (_, Def v _) = v `isUsedIn` all_uses

  -- Uses from the still-live functions are real.  Compute new definitions.
  let live_uses = useUnions (body_uses : map fst live_defs)
      new_defs = map (setFunDefUses live_uses . snd) live_defs

  -- Expose all uses except the locally defined functions
  putUses $ deleteUses (map definiendum new_defs) live_uses

  -- Add code size for the function definitions
  let def_code_size = sum $ map (funDefinitionSize . definiens) new_defs
  nudge def_code_size (return ())

  return (new_defs, new_body)

-- | Rebuild a function definition after DCE.
setFunDefUses :: UseMap -> FunDef -> FunDef 
setFunDefUses use_map (Def fname f) =
  let fuses = lookupUses fname use_map
      annotated_fun = setFunUses fuses f
  in Def fname $! annotated_fun

-- | Perform dead code elimination on a function.  Only the function body 
--   contributes to the code size.
dceFun :: DCE Fun
dceFun fun = do
  (body_size, body) <- tellSize $ dceStm (funBody fun)
  let fun' = setFunSize (codeSize body_size) $
             mkFun (funConvention fun) (funInlineRequest fun) (funFrameSize fun) (funParams fun) (funReturnTypes fun) body
  return fun'

-- | Perform dead code elimination on a data definition.  The data definition
--   is scanned to find out what variables it references.
dceDataDef :: DCE DataDef
dceDataDef (Def v (StaticData rec vals)) =
  (Def v . StaticData rec) <$> dceVals vals

assumeImportedArity impent m =
  case impent
  of ImportClosureFun ep _ ->
       assumeFunctionArity (importVar impent) (functionArity ep) m
     ImportPrimFun _ ty _ ->
       assumeFunctionArity (importVar impent) (length $ ftParamTypes ty) m
     ImportData _ _ -> m

assumeImportedArities imps m = foldr assumeImportedArity m imps

dceTopLevel :: [Import]         -- ^ Imported variables
            -> [GlobalDef]      -- ^ Global definitions
            -> [Var]            -- ^ Exported variables
            -> DCEM [GlobalDef]
dceTopLevel imps defs exports = assumeImportedArities imps $ do
  -- Perform DCE and find all uses
  (new_fun_defs, new_data_defs) <-
    dceDefGroup fun_defs (use_exports *> dce_data_defs)
  
  -- Don't need to compute uses or code size
  return (map GlobalFunDef new_fun_defs ++ map GlobalDataDef new_data_defs)
  where
    (fun_defs, data_defs) = partitionGlobalDefs defs

    -- All exported variables are used an unknown number of times
    use_exports = 
      putUses $ IntMap.fromList [(fromIdent $ varID v, ManyUses)
                                | v <- exports]

    dce_data_defs = mapM dceDataDef data_defs

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