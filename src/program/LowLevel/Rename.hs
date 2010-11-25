{-|
Methods for renaming variables in a module.
-}

module LowLevel.Rename
       (RnPolicy(..),
        Renaming,
        mkRenaming,
        renameStm,
        renameFun,
        renameInFunDef,
        renameModule
       )
where

import Control.Monad
import qualified Data.IntMap as IntMap
import Data.Maybe

import Gluon.Common.Error
import Gluon.Common.Identifier
import LowLevel.FreshVar
import LowLevel.Syntax
import Export

-- | A variable renaming
type Renaming = IntMap.IntMap Var

-- | Create a renaming from an association list
mkRenaming :: [(Var, Var)] -> Renaming
mkRenaming assocs =
  IntMap.fromList [(fromIdent $ varID from_v, to_v) | (from_v, to_v) <- assocs]

data RnPolicy =
    RenameEverything  -- ^ Rename everything except imported variables
  | RenameLocals      -- ^ Rename everything except global variables
  | RenameParameters  -- ^ Rename function parameters and let-bound variables, 
                      --   but not letrec-bound variables

type Rn = (RnPolicy, Renaming)

rnPolicy :: Rn -> RnPolicy
rnPolicy (p, _) = p

rnRenaming :: Rn -> Renaming
rnRenaming (_, rn) = rn

setRenaming :: Renaming -> Rn -> Rn
setRenaming rn (p, _) = (p, rn)

-- | Assign a fresh ID to this variable, and insert the assignment into the
--   renaming.
renameVariable :: Renaming -> Var -> FreshVarM (Renaming, Var)
renameVariable rn v = do
  v' <- newVar (varName v) (varType v)
  let rn' = IntMap.insert (fromIdent $ varID v) v' rn
  return (rn', v')

renameVariables :: Renaming -> [Var] -> FreshVarM (Renaming, [Var])
renameVariables rn vs = go rn [] vs
  where
    go rn rev_vs' (v:vs) = do
      (rn', v') <- renameVariable rn v
      go rn' (v':rev_vs') vs
    
    go rn rev_vs' [] =
      return (rn, reverse rev_vs')

renameParameters :: Rn -> [ParamVar] -> FreshVarM (Renaming, [ParamVar])
renameParameters rn param_vars =
  case rnPolicy rn
  of RenameEverything -> rename
     RenameLocals     -> rename
     RenameParameters -> rename
  where
    rename = renameVariables (rnRenaming rn) param_vars

renameLetrecFunction :: Rn -> Var -> FreshVarM (Renaming, Var)
renameLetrecFunction rn var =
  case rnPolicy rn
  of RenameEverything -> rename
     RenameLocals     -> rename
     RenameParameters -> don't
  where
    don't = return (rnRenaming rn, var)
    rename = renameVariable (rnRenaming rn) var

renameLetrecFunctions :: Rn -> [Var] -> FreshVarM (Renaming, [Var])
renameLetrecFunctions rn vars =
  case rnPolicy rn
  of RenameEverything -> rename
     RenameLocals     -> rename
     RenameParameters -> don't
  where
    don't = return (rnRenaming rn, vars)
    rename = renameVariables (rnRenaming rn) vars
  
renameGlobalEntities rn vars = 
  case rnPolicy rn
  of RenameEverything -> rename
     RenameLocals     -> don't
     RenameParameters -> don't
  where
    don't = return (rnRenaming rn, vars)
    rename = renameVariables (rnRenaming rn) vars

rnVar :: Renaming -> Var -> Var
rnVar rn v = fromMaybe v $ IntMap.lookup (fromIdent $ varID v) rn

rnVal :: Rn -> Val -> FreshVarM Val
rnVal rn value =
  case value
  of VarV v      -> return $ VarV (rnVar (rnRenaming rn) v)
     RecV rec vs -> RecV rec `liftM` rnVals rn vs
     LitV l      -> return $ LitV l
     LamV f      -> LamV `liftM` rnFun rn f

rnVals rn vs = mapM (rnVal rn) vs

rnAtom :: Rn -> Atom -> FreshVarM Atom
rnAtom rn atom =
  case atom
  of ValA vs            -> ValA `liftM` rnVals rn vs
     CallA conv op args -> CallA conv `liftM` rnVal rn op `ap` rnVals rn args
     PrimA prim args    -> PrimA prim `liftM` rnVals rn args
     PackA sr vs        -> PackA sr `liftM` rnVals rn vs
     UnpackA sr v       -> UnpackA sr `liftM` rnVal rn v

rnStm :: Rn -> Stm -> FreshVarM Stm
rnStm rn statement =
  case statement
  of LetE params rhs stm -> do
       rhs' <- rnAtom rn rhs
       (renaming, params') <- renameParameters rn params
       stm' <- rnStm (setRenaming renaming rn) stm
       return $ LetE params' rhs' stm'
     LetrecE defs stm -> do
       (renaming, definienda) <-
         renameLetrecFunctions rn $ map definiendum defs
       definientia <-
         mapM (rnFun (setRenaming renaming rn) . definiens) defs
       stm' <- rnStm (setRenaming renaming rn) stm
       return $ LetrecE (zipWith Def definienda definientia) stm'
     SwitchE scr alts -> do
       scr' <- rnVal rn scr
       alts' <- mapM rename_alt alts
       return $ SwitchE scr' alts'
     ReturnE atom ->
       ReturnE `liftM` rnAtom rn atom
  where
    rename_alt (tag, stm) = do
      stm' <- rnStm rn stm
      return (tag, stm')

rnFun :: Rn -> Fun -> FreshVarM Fun
rnFun rn f = do
  (renaming, params) <- renameParameters rn $ funParams f
  body <- rnStm (setRenaming renaming rn) $ funBody f
  return $ f {funParams = params, funBody = body}

-- | Rename the contents of a data definition.
rnStaticData :: Rn -> StaticData -> FreshVarM StaticData
rnStaticData rn (StaticData record values) = do
  values' <- rnVals rn values
  return $ StaticData record values'

rnExport :: Renaming -> (Var, ExportSig) -> (Var, ExportSig)
rnExport rn (v, sig) = (rnVar rn v, sig)

rnTopLevel :: Rn -> [GlobalDef] -> [(Var, ExportSig)]
           -> FreshVarM (Renaming, [GlobalDef], [(Var, ExportSig)])
rnTopLevel rn global_defs exports = do
  (rn', definienda) <- rename_globals
  global_defs' <- zipWithM (rename rn') definienda global_defs
  let exports' = map (rnExport (rnRenaming rn')) exports
  return (rnRenaming rn', global_defs', exports')
  where
    rename rn2 new_name global_def = 
      case global_def
      of GlobalFunDef (Def _ fun) -> do
           fun' <- rnFun rn2 fun
           return (GlobalFunDef (Def new_name fun'))
         GlobalDataDef (Def _ dat) -> do
           dat' <- rnStaticData rn2 dat
           return (GlobalDataDef (Def new_name dat'))

    -- Rename names of global functions and data
    rename_globals = do
      (renaming, definienda) <-
        renameGlobalEntities rn $ map globalDefiniendum global_defs
      let rn1 = setRenaming renaming rn
      return (rn1, definienda)

-- | Rename variables in a statement.  Start with the given renaming.
renameStm :: RnPolicy -> Renaming -> Stm -> FreshVarM Stm
renameStm policy rn stm = rnStm (policy, rn) stm

-- | Rename variables in a function
renameFun :: RnPolicy -> Fun -> FreshVarM Fun
renameFun policy fun = do
  rnFun (policy, IntMap.empty) fun
  
-- | Rename variables in a function definition.  The variable that is defined
-- by the definition isn't renamed.
renameInFunDef :: RnPolicy -> FunDef -> FreshVarM FunDef
renameInFunDef policy (Def v f) = do
  f' <- renameFun policy f
  return (Def v f')

-- | Rename variables in a module
renameModule :: RnPolicy -> Module -> FreshVarM Module
renameModule policy mod = do
  (_, defs, exports) <-
    rnTopLevel (policy, IntMap.empty) (moduleGlobals mod) (moduleExports mod)
  return $ mod {moduleGlobals = defs, moduleExports = exports}