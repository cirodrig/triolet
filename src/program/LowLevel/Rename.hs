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
        renameVal,
        renameStm,
        renameFun,
        renameEntryPoints,
        renameStaticData,
        renameImport,
        renameInFunDef,
        renameModule
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

import Common.Error
import Common.Identifier
import LowLevel.FreshVar
import LowLevel.Syntax
import Export

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
     RenameFunctions  -> don't
     RenameNothing    -> don't
  where
    rename = renameVariables (rnRenaming rn) param_vars
    don't = return (rnRenaming rn, param_vars)

renameLetrecFunction :: Rn -> Var -> FreshVarM (Renaming, Var)
renameLetrecFunction rn var =
  case rnPolicy rn
  of RenameEverything -> rename
     RenameLocals     -> rename
     RenameParameters -> don't
     RenameFunctions  -> rename
     RenameNothing    -> don't
  where
    don't = return (rnRenaming rn, var)
    rename = renameVariable (rnRenaming rn) var

renameLetrecFunctions :: Rn -> [Var] -> FreshVarM (Renaming, [Var])
renameLetrecFunctions rn vars =
  case rnPolicy rn
  of RenameEverything -> rename
     RenameLocals     -> rename
     RenameParameters -> don't
     RenameFunctions  -> rename
     RenameNothing    -> don't
  where
    don't = return (rnRenaming rn, vars)
    rename = renameVariables (rnRenaming rn) vars

renameGlobalFunction rn var = 
  case rnPolicy rn
  of RenameEverything -> rename
     RenameLocals     -> don't
     RenameParameters -> don't
     RenameFunctions  -> rename
     RenameNothing    -> don't
  where
    don't = return (rnRenaming rn, var)
    rename = renameVariable (rnRenaming rn) var

renameGlobalData rn var = 
  case rnPolicy rn
  of RenameEverything -> rename
     RenameLocals     -> don't
     RenameParameters -> don't
     RenameFunctions  -> don't
     RenameNothing    -> don't
  where
    don't = return (rnRenaming rn, var)
    rename = renameVariable (rnRenaming rn) var

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
     LetrecE (NonRec def) stm -> do
       definiens <- rnFun rn $ definiens def
       (renaming, definiendum) <-
         renameLetrecFunction rn $ definiendum def
       stm' <- rnStm (setRenaming renaming rn) stm
       return $ LetrecE (NonRec (Def definiendum definiens)) stm'
     LetrecE (Rec defs) stm -> do
       (renaming, definienda) <-
         renameLetrecFunctions rn $ map definiendum defs
       definientia <-
         mapM (rnFun (setRenaming renaming rn) . definiens) defs
       stm' <- rnStm (setRenaming renaming rn) stm
       return $ LetrecE (Rec $ zipWith Def definienda definientia) stm'
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

rnEntryPoints :: Renaming -> EntryPoints -> EntryPoints
rnEntryPoints rn (EntryPoints ty arity dir vec exa ine inf glo) =
  EntryPoints ty arity
  (rnVar rn dir) (fmap (rnVar rn) vec) (rnVar rn exa)
  (rnVar rn ine) (rnVar rn inf) (rnVar rn glo)

rnFun :: Rn -> Fun -> FreshVarM Fun
rnFun rn f = do
  let entry_points = fmap (rnEntryPoints (rnRenaming rn)) $ funEntryPoints f
  (renaming, params) <- renameParameters rn $ funParams f
  body <- rnStm (setRenaming renaming rn) $ funBody f
  return $ f { funEntryPoints = entry_points
             , funParams = params
             , funBody = body}

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
      (rn', group') <- rename_global_group rn id group
      (rn'', groups') <- rename_globals1 rn' groups
      return (rn'', group' : groups')
    
    rename_globals1 rn [] = return (rn, [])

    -- Rename one definition group
    rename_global_group in_rn hd (NonRec def) = do
      (rn, [v']) <- rename_global_defs in_rn [def]
      -- The definition cannot refer to itself, so use the original renaming.
      def' <- rename in_rn v' def
      return (rn, NonRec def')
 
    rename_global_group in_rn hd (Rec defs) = do
      -- Rename bound variables
      (rn, vs) <- rename_global_defs in_rn defs
      -- Rename definitions, which may refer to the bound variables
      defs' <- zipWithM (rename rn) vs defs
      return (rn, Rec defs')
    
    -- Rename the variables that are defined by some global definitions
    rename_global_defs in_rn (def : defs) = do
      (renaming, v) <-
        case def
        of GlobalFunDef (Def v _) -> renameGlobalFunction in_rn v
           GlobalDataDef (Def v _) -> renameGlobalData in_rn v
      (renaming', vs) <- rename_global_defs (setRenaming renaming in_rn) defs
      return (renaming', v : vs)
      
    rename_global_defs rn [] = return (rn, [])

    -- Rename a global definition.
    rename in_rn new_name global_def =
      case global_def
      of GlobalFunDef (Def _ fun) -> do
           fun' <- rnFun in_rn fun
           return (GlobalFunDef (Def new_name fun'))
         GlobalDataDef (Def _ dat) -> do
           dat' <- rnStaticData in_rn dat
           return (GlobalDataDef (Def new_name dat'))


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

renameImport :: RnPolicy -> Renaming -> Import -> FreshVarM Import
renameImport policy rn i = rnImport (policy, rn) i

-- | Rename variables in a function definition.  The variable that is defined
-- by the definition isn't renamed.
renameInFunDef :: RnPolicy -> FunDef -> FreshVarM FunDef
renameInFunDef policy (Def v f) = do
  f' <- renameFun policy emptyRenaming f
  return (Def v f')

-- | Rename variables in a module
renameModule :: RnPolicy -> Renaming -> Module -> FreshVarM Module
renameModule policy rn mod = do
  imports <- mapM (rnImport (policy, rn)) (moduleImports mod)
  (_, defs, exports) <- do
    rnTopLevel (policy, rn) (moduleGlobals mod) (moduleExports mod)
  return $ mod { moduleImports = imports
               , moduleGlobals = defs
               , moduleExports = exports}