{-|
Methods for renaming variables in a module.
-}

module LowLevel.Rename
       (RnPolicy(..),
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

data RnPolicy =
    RenameEverything  -- ^ Rename everything except imported variables
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
--   renaming.  The variable must not be externally defined.
renameVariable :: Renaming -> Var -> FreshVarM (Renaming, Var)
renameVariable rn v
  | varIsExternal v = internalError "renameVariable: Variable is external"
  | otherwise = do
      v' <- newVar (varName v) (varExternalName v) (varType v)
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
     RenameParameters -> rename
  where
    rename = renameVariables (rnRenaming rn) param_vars

renameLetrecFunction :: Rn -> Var -> FreshVarM (Renaming, Var)
renameLetrecFunction rn var =
  case rnPolicy rn
  of RenameEverything -> rename
     RenameParameters -> don't
  where
    don't = return (rnRenaming rn, var)
    rename = renameVariable (rnRenaming rn) var

renameLetrecFunctions :: Rn -> [Var] -> FreshVarM (Renaming, [Var])
renameLetrecFunctions rn vars =
  case rnPolicy rn
  of RenameEverything -> rename
     RenameParameters -> don't
  where
    don't = return (rnRenaming rn, vars)
    rename = renameVariables (rnRenaming rn) vars
  
-- Same renaming decision as for letrec
renameGlobalEntities = renameLetrecFunctions

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
  of ValA vs           -> ValA `liftM` rnVals rn vs
     CallA op args     -> CallA `liftM` rnVal rn op `ap` rnVals rn args
     PrimCallA op args -> PrimCallA `liftM` rnVal rn op `ap` rnVals rn args
     PrimA prim args   -> PrimA prim `liftM` rnVals rn args
     PackA sr vs       -> PackA sr `liftM` rnVals rn vs
     UnpackA sr v      -> UnpackA sr `liftM` rnVal rn v

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
         renameLetrecFunctions rn $ map funDefiniendum defs
       definientia <-
         mapM (rnFun (setRenaming renaming rn) . funDefiniens) defs
       stm' <- rnStm (setRenaming renaming rn) stm
       return $ LetrecE (zipWith FunDef definienda definientia) stm'
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

-- | Rename the contents of a data definition.  The data variable isn't
--   assigned a new name.
rnDataDef :: Rn -> DataDef -> FreshVarM DataDef
rnDataDef rn (DataDef v record values) = do
  values' <- rnVals rn values
  return $ DataDef v record values'

rnExport :: Renaming -> (Var, ExportSig) -> (Var, ExportSig)
rnExport rn (v, sig) = (rnVar rn v, sig)

rnTopLevel :: Rn -> [FunDef] -> [DataDef] -> [(Var, ExportSig)]
           -> FreshVarM (Renaming, [FunDef], [DataDef], [(Var, ExportSig)])
rnTopLevel rn fun_defs data_defs exports = do
  (rn', f_definienda, d_definienda) <- rename_globals

  -- Rename contents of functions
  f_definientia <- mapM (rnFun rn' . funDefiniens) fun_defs
  let fun_defs' = zipWith FunDef f_definienda f_definientia

  -- Rename contents of data definitions
  data_defs1 <- mapM (rnDataDef rn') data_defs
  let data_defs' = [DataDef v record values
                   | (v, DataDef _ record values) <-
                     zip d_definienda data_defs1]
                   
  let exports' = map (rnExport (rnRenaming rn')) exports

  return (rnRenaming rn', fun_defs', data_defs', exports')
  where
    -- Rename names of global functions and data
    rename_globals = do
      (renaming1, f_definienda) <-
        renameGlobalEntities rn $ map funDefiniendum fun_defs
      let rn1 = setRenaming renaming1 rn
      (renaming2, d_definienda) <-
        renameGlobalEntities rn1 $ map dataDefiniendum data_defs
      let rn2 = setRenaming renaming2 rn
      return (rn2, f_definienda, d_definienda)

-- | Rename variables in a function
renameFun :: RnPolicy -> Fun -> FreshVarM Fun
renameFun policy fun = do
  rnFun (policy, IntMap.empty) fun
  
-- | Rename variables in a function definition.  The variable that is defined
-- by the definition isn't renamed.
renameInFunDef :: RnPolicy -> FunDef -> FreshVarM FunDef
renameInFunDef policy (FunDef v f) = do
  f' <- renameFun policy f
  return (FunDef v f')

-- | Rename variables in a module
renameModule :: RnPolicy -> Module -> FreshVarM Module
renameModule policy mod = do
  (_, fdefs, ddefs, exports) <-
    rnTopLevel (policy, IntMap.empty)
    (moduleFunctions mod) (moduleData mod) (moduleExports mod)
  return $ mod { moduleFunctions = fdefs
               , moduleData = ddefs
               , moduleExports = exports}