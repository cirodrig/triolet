{-| Interface file code.

Interface files contain information about a module's exported symbols,
including definitions of symbols that may be inlined or propagated to
users.
-}

module LowLevel.InterfaceFile
       (Interface,
        createModuleInterface,
        addInterfaceToModuleImports)
where

import Prelude hiding(mapM)

import Control.Applicative
import Control.Monad hiding(forM, mapM)
import Data.Binary
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Data.Traversable

import Gluon.Common.Error
import Gluon.Common.Supply
import LowLevel.Binary
import LowLevel.Build
import LowLevel.Builtins
import LowLevel.CodeTypes
import LowLevel.FreshVar
import LowLevel.Inlining
import LowLevel.Label
import LowLevel.Rename
import LowLevel.Syntax
import Export
import Globals

-- | A definition that's being prepared for output to an interface file
type PreImport = Def PreImportData

-- | A symbol that's being prepared for output to an interface file
data PreImportData =
    PreImportFun !FunctionType !(Maybe Fun)
  | PreImportData !StaticData

renamePreImport :: Renaming -> PreImport -> FreshVarM PreImport
renamePreImport rn (Def v pi) =
  case pi
  of PreImportFun ft Nothing -> return $ Def v pi
     PreImportFun ft (Just f) -> do
       f' <- renameFun RenameNothing rn f
       return $ Def v $ PreImportFun ft (Just f')
     PreImportData sd -> do
       sd' <- renameStaticData RenameNothing rn sd
       return $ Def v $ PreImportData sd'

mkImport :: PreImport -> FreshVarM Import
mkImport pre_import = label `seq` -- Verify that label is valid
  case definiens pre_import
  of PreImportFun ft mfun
       | ftIsPrim ft ->
           return $ ImportPrimFun import_var ft mfun
       | ftIsClosure ft -> do
           ep <- mkGlobalEntryPoints ft label import_var
           return $ ImportClosureFun ep mfun
     PreImportData sdata ->
       return $ ImportData import_var (Just sdata)
  where
    import_var = definiendum pre_import

    label = case varName import_var
            of Just n  -> n
               Nothing -> internalError "mkImport: No label"

-------------------------------------------------------------------------------

data Interface =
  Interface
  { -- | Symbols imported by the interface.  These variables
    --   must not have a definition.
    ifaceImports :: [Import] 
    -- | Symbols exported by the interface.  These variables may have a
    --   definition.
  , ifaceExports :: [Import]
  }

instance Binary Interface where
  put (Interface imps exps) = put imps >> put exps
  get = Interface <$> get <*> get

-------------------------------------------------------------------------------
-- Creating an interface

-- | Given a module, create an interface containing the symbols it exports
--   to Pyon code.  Include values of functions and data that are small
--   enough to inline.  DCE should be run first to calculate code size.
--
--   Any global symbols that are mentioned in the exported code will become
--   exported symbols themselves.
createModuleInterface :: Module -> IO (Module, Interface)
createModuleInterface mod = do
  -- Find all exported symbols, transitively
  let export_vars = Set.fromList [v | (v, PyonExportSig) <- moduleExports mod]
      (pre_imports, _) = slurpExports export_vars $ moduleGlobals mod
      
  -- Rename all exported anonymous variables to new names
  renaming <- createLocalNames (moduleModuleName mod) (moduleNameSupply mod) $
              [v | Def v _ <- pre_imports, isNothing $ varName v]

  withTheLLVarIdentSupply $ \ll_supply -> runFreshVarM ll_supply $ do
    mod' <- renameModule RenameNothing renaming mod
    pre_imports' <- mapM (renamePreImport renaming) pre_imports

    -- Create the interface
    exports <- mapM mkImport pre_imports'
    let imports = map clearImportDefinition $ moduleImports mod
    let interface = Interface { ifaceImports = imports
                              , ifaceExports = exports}
        
    -- Extend the export list with the new exported variables
    let new_exports = [(v, PyonExportSig) | Def v _ <- pre_imports'
                                          , not $ v `Set.member` export_vars]
        mod'' = mod' {moduleExports = new_exports ++ moduleExports mod'}
    
    return (mod'', interface)

-- | Create a renaming that renames each member of the list to a
--   variable with a local ID.
createLocalNames :: ModuleName -> Supply LocalID -> [Var] -> IO Renaming
createLocalNames mod_name id_supply from_vars =
  withTheLLVarIdentSupply $ \ll_supply -> do
    rename_assocs <- forM from_vars $ \v -> do
      local_id <- supplyValue id_supply
      let label = anonymousPyonLabel mod_name local_id Nothing
      new_v <- runFreshVarM ll_supply $ newExternalVar label (varType v)
      return (v, new_v)
    return $ mkRenaming rename_assocs

-- | Scan the given exports to select additional variables for export.
slurpExports :: Set.Set Var -> [GlobalDef] -> ([PreImport], [GlobalDef])
slurpExports exported gdefs 
  | Set.null exported = ([], gdefs)
  | otherwise =
    let -- Find the exported definitions and convert them
        (export_defs, other_defs) = partition is_exported gdefs
        imports = map mkPreImport export_defs
        
        -- Find additional definitions mentioned by these
        other_def_vars = Set.fromList $ map globalDefiniendum gdefs
        additional_exported =
          (mconcat $ map findReferencedGlobals imports) other_def_vars
        
        -- Include the additional definitions
        (imports2, leftover) = slurpExports additional_exported other_defs
    in (imports ++ imports2, leftover)
  where
    is_exported gdef = globalDefiniendum gdef `Set.member` exported

{-
-- | Partition global definitions into those that are exported and those that
--   aren't
pickPyonExports :: Module -> ([GlobalDef], [GlobalDef])
pickPyonExports mod = partition is_exported $ moduleGlobals mos
  where
    exported_vars = [v | (v, PyonExportSig) <- moduleExports mod]
    is_exported d = globalDefiniendum d `elem` exported_vars-}
      
mkPreImport :: GlobalDef -> PreImport
mkPreImport (GlobalFunDef (Def v f)) =
  let f_val = if funSmallEnoughForInlining f then Just f else Nothing
  in Def v (PreImportFun (funType f) f_val)

mkPreImport (GlobalDataDef (Def v dat)) =
  Def v (PreImportData dat)
  
-------------------------------------------------------------------------------
-- Finding global variable references

-- | Given a set of global variables in the current module,
--   get the subset that is referenced by something.
type FindRefs = Set.Set Var -> Set.Set Var

findReferencedGlobals :: PreImport -> FindRefs
findReferencedGlobals (Def _ (PreImportFun _ Nothing)) = mempty
findReferencedGlobals (Def _ (PreImportFun _ (Just f))) = findRefsFun f
findReferencedGlobals (Def _ (PreImportData (StaticData _ vals))) =
  findRefsVals vals

findRefsVal value =
  case value
  of VarV v -> \dom -> if v `Set.member` dom then Set.singleton v else mempty
     RecV _ vs -> findRefsVals vs
     LitV _ -> mempty
     LamV f -> findRefsFun f

findRefsVals vs = mconcat $ map findRefsVal vs

findRefsAtom atom =
  case atom
  of ValA vs         -> findRefsVals vs
     CallA _ op args -> findRefsVals (op : args)
     PrimA _ vs      -> findRefsVals vs
     PackA _ vs      -> findRefsVals vs
     UnpackA _ v     -> findRefsVal v
  
findRefsStm stm =
  case stm
  of LetE _ rhs body ->
       findRefsAtom rhs `mappend` findRefsStm body
     LetrecE defs body ->
       mconcat (findRefsStm body : map (findRefsFun . definiens) defs)
     SwitchE v alts ->
       mconcat (findRefsVal v : map (findRefsStm . snd) alts)
     ReturnE atom -> findRefsAtom atom

findRefsFun f = findRefsStm $ funBody f

-------------------------------------------------------------------------------
-- Loading an interface

-- | Add an interface to a module's import set.  Variables in the 
--   interface will be renamed to be consistent with the database of
--   builtin variables and with the module.  The interface will be added
--   to the module's import list.
--
--   The module being updated should have gone through record flattening, 
--   and should not have gone through closure conversion.
addInterfaceToModuleImports :: Interface -> Module -> IO Module
addInterfaceToModuleImports iface mod = do
  let -- The set of all variables that the interface may share with
      -- the builtins and/or the module.  Since closure conversion hasn't 
      -- happened, we only care about a closure-based function's global
      -- closure.
      --
      -- Using a set also eliminates duplicate list entries. 
      import_variables =
        Set.toList $ Set.fromList $
        allBuiltins ++ map importVar (moduleImports mod)
  
  -- Rename variables in the interface
  (rn_imports, rn_exports) <- 
    withTheLLVarIdentSupply $ \id_supply -> runFreshVarM id_supply $ do
      renameInterface import_variables iface
  
  -- Insert imports into the module's imports, replacing the existing imports.
  -- Error out if a type mismatch is detected.
  let imports = rn_imports ++ rn_exports ++
                filter not_from_interface (moduleImports mod)
        where
          not_from_interface impent =
            let v = importVar impent
            in all ((v /=) . importVar) $ rn_exports
      
  return $ mod {moduleImports = imports}

-- | Rename an interface's imported and exported symbols, given the set of
--   variables that the interface's symbols should be renamed to.
--
--   Exported symbols are renamed to one of the given variables, if one has
--   the same label, or else to a new variable name.
--
--   Imported symbols are discarded if one of the given variables has the
--   same label, or else renamed to a new variable name.
renameInterface :: [Var] -> Interface -> FreshVarM ([Import], [Import])
renameInterface import_variables iface = do
  -- Create new variables
  i_results <- mapM pick_renaming_or_discard $ ifaceImports iface
  let (new_i_variables, orig_imports) = unzip $ catMaybes i_results
  let orig_exports = ifaceExports iface
  new_e_variables <- mapM pick_renamed_name $ map importVar orig_exports

  -- Create renaming
  let renaming = mkRenaming $
                 zip (map importVar orig_exports) new_e_variables ++
                 zip (map importVar orig_imports) new_i_variables
  
  -- Apply renaming
  new_imports <- mapM (rename_import renaming) orig_imports
  new_exports <- mapM (rename_import renaming) orig_exports
  return (new_imports, new_exports)
  where
    -- Map from variable name to variable
    import_variable_labels =
      Map.fromList [(get_label v, v) | v <- import_variables]
      where
        get_label v =
          case varName v
          of Just lab -> lab
             Nothing  -> internalError $ "renameInterface: " ++
                         "Imported variable has no label"

    -- Decide what to rename an exported variable to.  Discard if there's
    -- a preexisting variable with the same name.
    -- Otherwise create a new variable.
    pick_renaming_or_discard impent
      | Just global_var <- Map.lookup lab import_variable_labels =
          return Nothing
      | otherwise = do
          -- Rename to a new variable with the same label
          new_var <- newExternalVar lab (varType $ importVar impent)
          return $ Just (new_var, impent)
      where
        lab = case varName $ importVar impent
              of Just l  -> l
                 Nothing -> internalError $ "renameInterface: " ++
                            "Interface variable has no label"
    
    -- Decide what to rename an exported variable to.  Rename to the
    -- preexisting variable with the same name, if one exists.
    -- Otherwise create a new variable.
    pick_renamed_name interface_var
      | Just global_var <- Map.lookup lab import_variable_labels =
          -- Rename to the preexisting variable with the same label
          return global_var
      | otherwise =
          -- Rename to a new variable with the same label
          newExternalVar lab (varType interface_var)
      where
        lab = case varName interface_var
              of Just l  -> l
                 Nothing -> internalError $ "renameInterface: " ++
                            "Interface variable has no label"

    -- Rename within an imported module
    rename_import renaming impent =
      let renamed_var = case getRenamedVar (importVar impent) renaming
                        of Just v -> v
                           Nothing -> internalError "renameInterface"
          Just lab = varName renamed_var
      in case impent
         of ImportClosureFun ep mfun -> do
              ep' <- mkGlobalEntryPoints (entryPointsType ep) lab renamed_var
              mfun' <- mapM (renameFun RenameEverything renaming) mfun
              return $ ImportClosureFun ep' mfun'
            ImportPrimFun _ t mfun -> do
              mfun' <- mapM (renameFun RenameEverything renaming) mfun
              return $ ImportPrimFun renamed_var t mfun'
            ImportData _ Nothing ->
              return $ ImportData renamed_var Nothing
            ImportData _ (Just (StaticData rec values)) -> do
              values' <- mapM (renameVal RenameEverything renaming) values
              return $ ImportData renamed_var (Just (StaticData rec values'))
      