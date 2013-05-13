{-|
Methods for renaming variables in a module.
-}

module LowLevel.Rename
       (-- * Free variables
        FreeVars, MkFreeVars,
        HasScope(..),
        computeFreeVars,
        maskFreeVar, maskFreeVars,

        -- * Renaming
        RnPolicy(..),
        Renaming,
        lookupRenamedVar,
        mkRenaming,
        emptyRenaming,
        getRenamedVar,
        renameVar,
        renameVal,
        renameStm,
        renameFun,
        renameEntryPoints,
        renameStaticData,
        renameImport,
        renameInFunDef,
        renameModule,
        renameModuleGlobals
       )
where

import Prelude hiding(mapM)

import Control.Monad hiding(mapM)
import qualified Data.IntMap as IntMap
import Data.List(foldl')
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Data.Traversable
import Debug.Trace

import Common.Error
import Common.Identifier
import Common.MonadLogic
import LowLevel.Builtins(allBuiltins)
import LowLevel.FreshVar
import LowLevel.Syntax
import Export

allBuiltinsSet = Set.fromList allBuiltins

-------------------------------------------------------------------------------
-- Free variables

type FreeVars = Set.Set Var

newtype MkFreeVars = MkFreeVars (Set.Set Var -> Set.Set Var)

-- | 'MkFreeVars' is a monoid under composition.
--   @x `mappend` y@ performs @x@, then @y@.
instance Monoid MkFreeVars where
  mempty = MkFreeVars id
  MkFreeVars f1 `mappend` MkFreeVars f2 = MkFreeVars (f2 . f1)
  mconcat ms = MkFreeVars $ \s -> foldl' (\s (MkFreeVars f) -> f s) s ms

computeFreeVars :: MkFreeVars -> FreeVars
computeFreeVars (MkFreeVars f) = f Set.empty

putFreeVar :: Var -> MkFreeVars
putFreeVar v = MkFreeVars (Set.insert v)

maskFreeVar :: Var -> MkFreeVars -> MkFreeVars
maskFreeVar v (MkFreeVars f) = MkFreeVars $ \s -> Set.delete v (f s)

maskFreeVars :: [Var] -> MkFreeVars -> MkFreeVars
maskFreeVars vs (MkFreeVars f) =
  MkFreeVars $ \s -> foldl' (flip Set.delete) (f s) vs

class HasScope a where
  freeVars :: a -> MkFreeVars

instance HasScope a => HasScope [a] where
  freeVars xs = mconcat $ map freeVars xs

instance HasScope Val where
  freeVars (VarV v)    = putFreeVar v
  freeVars (RecV _ vs) = freeVars vs
  freeVars (LitV _)    = mempty

instance HasScope Atom where
  freeVars (ValA vs)      = freeVars vs
  freeVars (CallA _ v vs) = freeVars (v:vs)
  freeVars (PrimA _ vs)   = freeVars vs
  freeVars (PackA _ vs)   = freeVars vs
  freeVars (UnpackA _ v)  = freeVars v

instance HasScope Stm where
  freeVars (LetE params rhs body) =
    freeVars rhs `mappend` maskFreeVars params (freeVars body)

  freeVars (LetrecE (NonRec (Def v f)) body) =
    freeVars f `mappend` maskFreeVar v (freeVars body)

  freeVars (LetrecE (Rec defs) body) =
    let vars = map definiendum defs
        funs = map definiens defs
    in maskFreeVars vars (freeVars funs `mappend` freeVars body)

  freeVars (SwitchE scr alts) =
    freeVars scr `mappend` mconcat [freeVars s | (_, s) <- alts]

  freeVars (ReturnE atom) = freeVars atom

  freeVars (ThrowE val) = freeVars val

instance HasScope a => HasScope (FunBase a) where
  freeVars f = maskFreeVars (funParams f) $ freeVars (funBody f)

-------------------------------------------------------------------------------
-- Definientia

-- | The definienda of a definition
data Definienda = SingleD !Var | MultipleD !EntryPoints

globalDefinienda :: GlobalDef -> Definienda
globalDefinienda (GlobalFunDef (Def v fdef)) =
  case funEntryPoints fdef
  of Nothing -> SingleD v
     Just ep | v /= globalClosure ep -> internalError "globalDefinienda"
             | otherwise             -> MultipleD ep
               
globalDefinienda (GlobalDataDef (Def v _)) = SingleD v

setGlobalDefinienda :: Definienda -> GlobalDef -> GlobalDef
setGlobalDefinienda (SingleD v) (GlobalFunDef (Def _ fdef)) =
  GlobalFunDef $ Def v fdef

setGlobalDefinienda (SingleD v) (GlobalDataDef (Def _ d)) =
  GlobalDataDef $ Def v d

setGlobalDefinienda (MultipleD ep) (GlobalFunDef (Def _ fdef)) =
  GlobalFunDef $ Def (globalClosure ep) (fdef {funEntryPoints = Just ep})

localDefinienda :: FunDef -> Definienda
localDefinienda (Def v fdef) =
  case funEntryPoints fdef
  of Nothing -> SingleD v
     Just ep | v /= globalClosure ep -> traceShow v $ internalError "localDefinienda"
             | otherwise             -> MultipleD ep

setLocalDefinienda :: Definienda -> FunDef -> FunDef
setLocalDefinienda (SingleD v)    (Def _ f) =
  Def v f

setLocalDefinienda (MultipleD ep) (Def _ f) =
  Def (globalClosure ep) (f {funEntryPoints = Just ep})

-------------------------------------------------------------------------------

-- | A variable renaming
type Renaming = IntMap.IntMap Var

lookupRenamedVar :: Renaming -> Var -> Maybe Var
lookupRenamedVar rn v = IntMap.lookup (fromIdent $ varID v) rn

-- | Create a renaming from an association list
mkRenaming :: [(Var, Var)] -> Renaming
mkRenaming assocs =
  IntMap.fromList [(fromIdent $ varID from_v, to_v) | (from_v, to_v) <- assocs]

-- | An empty renaming
emptyRenaming :: Renaming
emptyRenaming = IntMap.empty

getRenamedVar :: Var -> Renaming -> Maybe Var
getRenamedVar v m = IntMap.lookup (fromIdent $ varID v) m

data RnPolicy =
    RenameEverything  -- ^ Rename everything except imported variables
  | RenameLocals      -- ^ Rename everything except global variables
  | RenameParameters  -- ^ Rename function parameters and let-bound variables, 
                      --   but not letrec-bound variables
  | RenameFunctions   -- ^ Rename function names bound by a 'Def' only
  | RenameNothing     -- ^ Don't rename anything; only apply the given renaming
    deriving(Eq)

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
  v' <- newClonedVar v
  let rn' = IntMap.insert (fromIdent $ varID v) v' rn
  return (rn', v')

renameVariables :: Renaming -> [Var] -> FreshVarM (Renaming, [Var])
renameVariables rn vs = mapAccumM renameVariable rn vs

-- | Assign a fresh ID to all variables in the 'EntryPoints',
--   and insert the assignments into the renaming.
renameEntryPointsVariables :: Renaming -> EntryPoints
                           -> FreshVarM (Renaming, EntryPoints)
renameEntryPointsVariables rn ep = do
  (rn', _) <- renameVariables rn $ entryPointsVars ep
  return (rn', rnEntryPoints rn' ep)

renameDefinienda rn (SingleD var) = do
  (rn', var') <- renameVariable rn var
  return (rn', SingleD var')
  
renameDefinienda rn (MultipleD ep) = do
  (rn', ep') <- renameEntryPointsVariables rn ep
  return (rn', MultipleD ep')

renameParameters :: Rn -> [ParamVar] -> FreshVarM (Renaming, [ParamVar])
renameParameters rn param_vars =
  case rnPolicy rn
  of RenameEverything -> rename
     RenameLocals     -> rename
     RenameParameters -> rename
     RenameFunctions  -> don't
     RenameNothing    -> don't
  where
    rename = renameVariables (rnRenaming rn) param_vars
    don't = return (rnRenaming rn, param_vars)

renameLetrecFunction :: Rn -> Definienda -> FreshVarM (Renaming, Definienda)
renameLetrecFunction rn da =
  case rnPolicy rn
  of RenameEverything -> rename
     RenameLocals     -> rename
     RenameParameters -> don't
     RenameFunctions  -> rename
     RenameNothing    -> don't
  where
    don't = return (rnRenaming rn, da)
    rename = renameDefinienda (rnRenaming rn) da

renameLetrecFunctions :: Rn -> [Definienda] -> FreshVarM (Renaming, [Definienda])
renameLetrecFunctions rn das = mapAccumM rename (rnRenaming rn) das
  where rename r d = renameLetrecFunction (setRenaming r rn) d

renameGlobalDef :: Rn -> Definienda -> FreshVarM (Renaming, Definienda)
renameGlobalDef rn definientia =
  case rnPolicy rn
  of RenameEverything -> rename
     RenameLocals     -> don't
     RenameParameters -> don't
     RenameFunctions  -> rename
     RenameNothing    -> don't
  where
    -- Even if we're not renaming, it's possible that a global variable has
    -- been given a name because we're merging with another module.
    -- Consequently, it must be renamed.
    don't = return (rnRenaming rn, rnDefinienda (rnRenaming rn) definientia)

    rename
      -- Don't rename built-in variables      
      | global_name `Set.member` allBuiltinsSet = don't
      | otherwise = renameDefinienda (rnRenaming rn) definientia

    global_name = case definientia
                  of SingleD v    -> v
                     MultipleD ep -> globalClosure ep

renameGlobalDefs :: Rn -> [Definienda] -> FreshVarM (Renaming, [Definienda])
renameGlobalDefs rn das = mapAccumM rename (rnRenaming rn) das
  where rename r d = renameGlobalDef (setRenaming r rn) d

rnVar :: Renaming -> Var -> Var
rnVar rn v = fromMaybe v $ IntMap.lookup (fromIdent $ varID v) rn

rnVal :: Rn -> Val -> Val
rnVal rn value =
  case value
  of VarV v      -> VarV (rnVar (rnRenaming rn) v)
     RecV rec vs -> RecV rec $ rnVals rn vs
     LitV l      -> LitV l

rnVals rn vs = map (rnVal rn) vs

rnAtom :: Rn -> Atom -> FreshVarM Atom
rnAtom rn atom =
  case atom
  of ValA vs            -> return $ ValA (rnVals rn vs)
     CallA conv op args -> return $ CallA conv (rnVal rn op) (rnVals rn args)
     PrimA prim args    -> return $ PrimA prim (rnVals rn args)
     PackA sr vs        -> return $ PackA sr (rnVals rn vs)
     UnpackA sr v       -> return $ UnpackA sr (rnVal rn v)

rnStm :: Rn -> Stm -> FreshVarM Stm
rnStm rn statement =
  case statement
  of LetE params rhs stm -> do
       rhs' <- rnAtom rn rhs
       (renaming, params') <- renameParameters rn params
       stm' <- rnStm (setRenaming renaming rn) stm
       return $ LetE params' rhs' stm'
     LetrecE group stm ->
       rnLocalGroup rn group stm
     SwitchE scr alts -> do
       let scr' = rnVal rn scr
       alts' <- mapM rename_alt alts
       return $ SwitchE scr' alts'
     ReturnE atom ->
       ReturnE `liftM` rnAtom rn atom
     ThrowE val ->
       return $ ThrowE (rnVal rn val)
  where
    rename_alt (tag, stm) = do
      stm' <- rnStm rn stm
      return (tag, stm')

rnLocalGroup :: Rn -> Group FunDef -> Stm -> FreshVarM Stm
rnLocalGroup rn group stm = do
  (renaming, group') <- rnLocalGroupDefs rn group
  stm' <- rnStm (setRenaming renaming rn) stm
  return $ LetrecE group' stm'

rnLocalGroupDefs rn (NonRec def) = do
  -- Rename the function body first, then rename the bound variables
  rn_fun <- rnFun rn $ definiens def
  let def1 = def {definiens = rn_fun}
  (renaming, rn_da) <- renameLetrecFunction rn $ localDefinienda def
  let def2 = setLocalDefinienda rn_da def1
  return (renaming, NonRec def2)

rnLocalGroupDefs rn (Rec defs) = do
  -- Rename bound varibles, then functions
  (renaming, rn_das) <- renameLetrecFunctions rn $ map localDefinienda defs
  rn_funs <- mapM (rnFun (setRenaming renaming rn)) $ map definiens defs
  let defs' = [setLocalDefinienda da $ def {definiens = fun}
              | (def, da, fun) <- zip3 defs rn_das rn_funs]
  return (renaming, Rec defs')

rnEntryPoints :: Renaming -> EntryPoints -> EntryPoints
rnEntryPoints rn (EntryPoints ty arity dir vec exa ine inf glo) =
  EntryPoints ty arity
  (rnVar rn dir) (fmap (rnVar rn) vec) (rnVar rn exa)
  (rnVar rn ine) (rnVar rn inf) (rnVar rn glo)

rnDefinienda rn (SingleD v)   = SingleD (rnVar rn v)
rnDefinienda rn (MultipleD v) = MultipleD (rnEntryPoints rn v)

rnFun :: Rn -> Fun -> FreshVarM Fun
rnFun rn f = do
  (renaming, params) <- renameParameters rn $ funParams f
  body <- rnStm (setRenaming renaming rn) $ funBody f
  return $ f {funParams = params, funBody = body}

-- | Rename the contents of a data definition.
rnStaticData :: Rn -> StaticData -> FreshVarM StaticData
rnStaticData rn (StaticData val) = return $ StaticData (rnVal rn val)

-- | Rename variables in an import specification.
--
--   If the imported variable has been assigned a new name, it will be
--   updated to the new name.  It won't be assigned a new name here.
rnImport :: Rn -> Import -> FreshVarM Import
rnImport rn impent =
  case impent
  of ImportClosureFun ep mf -> do
       let ep' = rnEntryPoints (rnRenaming rn) ep
       mf' <- mapM (rnFun rn) mf
       return $ ImportClosureFun ep' mf'
     ImportPrimFun v ft mf -> do
       let v' = rnVar (rnRenaming rn) v
       mf' <- mapM (rnFun rn) mf
       return $ ImportPrimFun v' ft mf'       
     ImportData v msdata -> do
       let v' = rnVar (rnRenaming rn) v
       msdata' <- mapM (rnStaticData rn) msdata
       return $ ImportData v' msdata'

rnExport :: Renaming -> (Var, ExportSig) -> (Var, ExportSig)
rnExport rn (v, sig) = (rnVar rn v, sig)

-- | Rename the top-level definitions in a module.
--   Variables defined at this level will be renamed if they're
--   present in the given renaming.
rnTopLevel :: Rn -> [Group GlobalDef] -> [(Var, ExportSig)]
           -> FreshVarM (Renaming, [Group GlobalDef], [(Var, ExportSig)])
rnTopLevel rn global_defs exports = do
  -- Rename the defined variables
  (rn', global_defs') <- rename_globals1 rn global_defs
  let exports' = map (rnExport (rnRenaming rn')) exports
  return (rnRenaming rn', global_defs', exports')
  where
    -- Rename names of global functions and data
    rename_globals1 :: Rn
                    -> [Group GlobalDef]
                    -> FreshVarM (Rn, [Group GlobalDef])
    rename_globals1 rn (group : groups) = do
      (renaming, group') <- rnGlobalGroupDefs rn group
      (rn'', groups') <- rename_globals1 (setRenaming renaming rn) groups
      return (rn'', group' : groups')
    
    rename_globals1 rn [] = return (rn, [])

rnGlobalGroupDefs :: Rn -> Group GlobalDef
                  -> FreshVarM (Renaming, Group GlobalDef)
rnGlobalGroupDefs rn (NonRec def) = do
  -- Rename the body first, then rename the bound variables
  rn_ens <- rnGlobalDefiniens rn def
  (renaming, rn_da) <- renameGlobalDef rn $ globalDefinienda def
  let def2 = rebuildGlobalDef rn_da rn_ens
  return (renaming, NonRec def2)

rnGlobalGroupDefs rn (Rec defs) = do
  -- Rename the bound variables, then the definitions
  (renaming, rn_das) <- renameGlobalDefs rn $ map globalDefinienda defs
  rn_enss <- mapM (rnGlobalDefiniens (setRenaming renaming rn)) defs
  let defs' = zipWith rebuildGlobalDef rn_das rn_enss
  return (renaming, Rec defs')

rnGlobalDefiniens rn (GlobalFunDef (Def v f)) = do
  f' <- rnFun rn f
  return $ Left $ Def v f'

rnGlobalDefiniens rn (GlobalDataDef (Def v d)) = do
  d' <- rnStaticData rn d
  return $ Right $ Def v d'

rebuildGlobalDef da (Left (Def v f)) =
  setGlobalDefinienda da (GlobalFunDef (Def v f))

rebuildGlobalDef da (Right (Def v d)) =
  setGlobalDefinienda da (GlobalDataDef (Def v d))

-- | Apply a renaming to a variable, and return the renamed variable.
renameVar :: Renaming -> Var -> Var
renameVar rn v = fromMaybe v $ lookupRenamedVar rn v

-- | Rename variables in a value.  Start with the given renaming.
renameVal :: RnPolicy -> Renaming -> Val -> Val
renameVal policy rn val = rnVal (policy, rn) val

-- | Rename variables in a statement.  Start with the given renaming.
renameStm :: RnPolicy -> Renaming -> Stm -> FreshVarM Stm
renameStm policy rn stm = rnStm (policy, rn) stm

-- | Rename variables in a function
renameFun :: RnPolicy -> Renaming -> Fun -> FreshVarM Fun
renameFun policy rn fun = rnFun (policy, rn) fun

renameEntryPoints :: RnPolicy -> Renaming -> EntryPoints -> EntryPoints
renameEntryPoints policy rn ep = rnEntryPoints rn ep

-- | Rename variables in a static data value
renameStaticData :: RnPolicy -> Renaming -> StaticData -> FreshVarM StaticData
renameStaticData policy rn d = rnStaticData (policy, rn) d

-- | Rename variables in an import declaration.  Variables defined by
--   the import declaration are also renamed, if present in the renaming.
renameImport :: RnPolicy -> Renaming -> Import -> FreshVarM Import
renameImport policy rn i = rnImport (policy, rn) i

-- | Rename variables in a function definition.  The variable that is defined
-- by the definition isn't renamed.
renameInFunDef :: RnPolicy -> FunDef -> FreshVarM FunDef
renameInFunDef policy (Def v f) = do
  f' <- renameFun policy emptyRenaming f
  return (Def v f')

-- | Rename some of the variables defined in a module
renameModule :: RnPolicy -> Module -> FreshVarM Module
renameModule policy mod = do
  -- Since 'emptyRenaming' is used as the initial renaming, the
  -- top-level definitions will either keep their original name or be
  -- given a fresh name
  imports <- mapM (rnImport (policy, emptyRenaming)) (moduleImports mod)
  (_, defs, exports) <- do
    rnTopLevel (policy, emptyRenaming) (moduleGlobals mod) (moduleExports mod)
  return $ mod { moduleGlobals = defs
               , moduleExports = exports}
 
-- | Rename some of the variables in a module.  Also apply the given 
--   renaming to global variables defined within the module.
renameModuleGlobals :: RnPolicy -> Renaming -> Module -> FreshVarM Module
renameModuleGlobals policy rn mod
  | policy == RenameFunctions || policy == RenameEverything =
    -- We cannot both use the given mapping and assign fresh names to globals.
    -- 'renameGlobalDef' must not assign fresh names. 
    -- See 'don't' in 'renameGlobalDef'.
    internalError "renameModuleGlobals: Invalid arguments"
      
  | otherwise = do
    imports <- mapM (rnImport (policy, rn)) (moduleImports mod)
    (_, defs, exports) <- do
      rnTopLevel (policy, rn) (moduleGlobals mod) (moduleExports mod)
    return $ mod { moduleImports = imports
                 , moduleGlobals = defs
                 , moduleExports = exports}