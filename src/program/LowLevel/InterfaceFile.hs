{-| Interface file code.

Interface files contain information about a module's exported symbols,
including definitions of symbols that may be inlined or propagated to
users.
-}

module LowLevel.InterfaceFile
       (Interface,
        pprInterface,
        createModuleInterface,
        addInterfaceToModuleImports,
        removeSelfImports)
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
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Supply
import Common.Label
import LowLevel.Binary
import LowLevel.Build
import LowLevel.Builtins
import LowLevel.CodeTypes
import LowLevel.FreshVar
import LowLevel.Inlining2
import LowLevel.Rename
import LowLevel.Print
import LowLevel.Syntax
import Export
import Globals

-- | A lookup table from labels to variables.  This table is used for
--   unifying variables that have the same label
type LabelMap = Map.Map Label Var

-- | Create a label map from a list of variables.
--   Order is important: if there are multiple variables with the same
--   label, the last one will be in the map.
labelMap :: [Var] -> LabelMap
labelMap vs = Map.fromList $ map assoc vs
  where
    assoc v = let !label = externVarName v in (label, v)

-- | Take the subset of the 'labelMap' whose labels match one of the given
--   variables
labelMapRestriction :: LabelMap -> [Var] -> LabelMap
labelMapRestriction m vars =
  Map.intersection m $ labelMap vars

-- | Check whether the given externally visible variable's label
--   is a key in the label map
labelMapContains :: LabelMap -> Var -> Bool
labelMapContains m v =
  let !label = externVarName v in label `Map.member` m

labelMapDoesn'tContain :: LabelMap -> Var -> Bool
labelMapDoesn'tContain m v = not $ labelMapContains m v

-- | Rename a variable by looking up its label in the label map.
--   If label is not found, create a fresh variable ID.
renameExternallyVisibleVar :: LabelMap -> Var -> FreshVarM Var
renameExternallyVisibleVar m v =
  case Map.lookup lab m
  of Just v' -> return v'
     Nothing -> newExternalVar lab (varType v)
  where
    lab = externVarName v

-- | Get the label of a variable that is externally visible.
--   The variable must have a label.
externVarName v =
  case varName v
  of Just lab -> lab
     Nothing  -> internalError $ "Externally visible variable has no label"

-- | A definition that's being prepared for output to an interface file
type PreImport = Def PreImportData

-- | A symbol that's being prepared for output to an interface file
data PreImportData =
    PreImportFun !FunctionType !(Maybe EntryPoints) !(Maybe Fun)
  | PreImportData !StaticData

renamePreImport :: Renaming -> PreImport -> FreshVarM PreImport
renamePreImport rn (Def v pi) = do
  pi' <- case pi
         of PreImportFun ft m_ep m_f -> do
              let m_ep' = fmap (renameEntryPoints RenameNothing rn) m_ep
              m_f' <- mapM (renameFun RenameNothing rn) m_f
              return $ PreImportFun ft m_ep' m_f'
            PreImportData sd -> do
              sd' <- renameStaticData RenameNothing rn sd
              return $ PreImportData sd'
  let v' = fromMaybe v $ lookupRenamedVar rn v
  return $ Def v' pi'

mkImport :: PreImport -> FreshVarM Import
mkImport pre_import = label `seq` -- Verify that label is valid
  case definiens pre_import
  of PreImportFun ft m_ep mfun ->
       case ftConvention ft
       of PrimCall ->
            return $ ImportPrimFun import_var ft mfun
          ClosureCall -> do
            let Just ep = m_ep
            return $ ImportClosureFun ep mfun
          JoinCall ->
            internalError "Imported function is a join point"
     PreImportData sdata ->
       return $ ImportData import_var (Just sdata)
  where
    import_var = definiendum pre_import

    label = case varName import_var
            of Just n  -> n
               Nothing -> internalError "mkImport: No label"

-------------------------------------------------------------------------------

-- | A module interface, declaring the symbols imported and exported by a
--   module.  A variable appears in the export list (possibly with a
--   definition) if it is defined by the module.  A variable appears in the
--   import list if it is used by the module.  A variable never appears in
--   both lists.
--
--   The invariants on variable IDs are not maintained across modules or
--   module interfaces.  Specifically, most of the compiler assumes that
--   every variable has a unique ID, and the global ID counter is larger
--   than the largest variable ID.  A module interface loaded from a file
--   doesn't necessarily satisfy the invariant.  The
--   'addInterfaceToModuleExports' function renames variables to
--   re-establish the invariant.
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

pprInterface :: Interface -> Doc
pprInterface iface =
  text "Imports:" $$ vcat (map pprImport $ ifaceImports iface) $$
  text "Exports:" $$ vcat (map pprImport $ ifaceExports iface) 

-------------------------------------------------------------------------------
-- Creating an interface

-- | Given a module, create an interface containing the symbols it exports
--   to Triolet code.  Include values of functions and data that are small
--   enough to inline.  DCE should be run first to calculate code size.
--
--   Any global symbols that are mentioned in the exported code will become
--   exported symbols themselves.
createModuleInterface :: Module -> IO (Module, Interface)
createModuleInterface pre_mod = do
  -- Find externally visible variables
  let (mod, pre_imports, _) = slurpExports pre_mod

  -- Rename all exported variables
  (renaming, mod') <- renameExternNames mod
  pre_imports' <- 
    withTheLLVarIdentSupply $ \ll_supply -> runFreshVarM ll_supply $ do
      mapM (renamePreImport renaming) pre_imports

  -- Create the interface
  interface <-
    withTheLLVarIdentSupply $ \ll_supply -> runFreshVarM ll_supply $ do
      exports <- mapM mkImport pre_imports'
      
      -- If a symbol is in the export list, it shouldn't be in the import
      -- list too.  (Really, it should be an error if a symbol is ever in
      -- both lists.)
      let imports = filter not_in_exports $
                    map clearImportDefinition $ moduleImports mod'
            where
              not_in_exports impent =
                all ((importVar impent /=) . importVar) exports

      return $ Interface { ifaceImports = imports
                         , ifaceExports = exports}

  -- DEBUG: Print the interface
  when False $ print $
    text ("Module interface of " ++ showModuleName (moduleModuleName mod)) $$
    pprInterface interface

  return (mod', interface)

-- | Rename each non-external variable in the list to a new,
--   externally visible name.
createExternNames :: ModuleName -> Supply LocalID -> [Var] -> IO Renaming
createExternNames mod_name id_supply from_vars =
  withTheLLVarIdentSupply $ \ll_supply -> do
    fmap mkRenaming $ mapM (mk_rename_assoc ll_supply) from_vars
    where
      mk_rename_assoc ll_supply v = do
        label <- case varName v
                 of Just label -> return label
                    Nothing -> do
                      local_id <- supplyValue id_supply
                      return $ anonymousLabel mod_name local_id Nothing
        new_v <- runFreshVarM ll_supply $ newExternalVar label (varType v)
        return (v, new_v)

-- | Rename all the module's exported variables to externally visible names.
--   The set of exported variables should have been expanded with
--   'slurpExports'.
renameExternNames :: Module -> IO (Renaming, Module)
renameExternNames mod = do
  -- Rename all exported variables that aren't already external
  let exported_local_vars =
        [v | (v, _) <- moduleExports mod, not $ varIsExternal v]
  renaming <- createExternNames (moduleModuleName mod) (moduleNameSupply mod)
              exported_local_vars

  -- Apply the renaming to the module
  withTheLLVarIdentSupply $ \ll_supply -> runFreshVarM ll_supply $ do
    mod1 <- renameModule RenameNothing renaming mod
    let mod2 = renameGlobalDefinitions renaming mod1
    return (renaming, mod2)

-- | Replace the globally defined variables that are in the renaming.
--   All other appearances of the variables have already been renamed.
renameGlobalDefinitions renaming mod =
  mod {moduleGlobals = map (fmap rename_global_def) $ moduleGlobals mod}
  where
    rename_global_def (GlobalFunDef def)
      | Just v <- lookupRenamedVar renaming $ definiendum def =
          GlobalFunDef (def {definiendum = v})
      | otherwise =
          GlobalFunDef def
    rename_global_def (GlobalDataDef def)
      | Just v <- lookupRenamedVar renaming $ definiendum def =
          GlobalDataDef (def {definiendum = v})
      | otherwise =
          GlobalDataDef def

-- | Scan the module to find all variables that are visible to other
--   modules.  These include the exported variables and any variables
--   that may show up due to inlining.
--   Add the visible variables to the export list.
--   Return the new module, the set of exported definitions, and the set of
--   non-exported definitions.
slurpExports :: Module -> (Module, [PreImport], [GlobalDef])
slurpExports mod = let
  -- Start with the variables that are explicitly exported
  declared_export_vars =
    Set.fromList [v | (v, TrioletExportSig) <- moduleExports mod]

  -- Add all reachable variables
  (export_vars, pre_imports, other_globals) =
    let global_defs = concatMap groupMembers $ moduleGlobals mod
    in slurpExports' Set.empty declared_export_vars global_defs

  -- Construct the module's new export list
  new_export_vars = export_vars Set.\\ declared_export_vars
  exports = [(v, TrioletExportSig) | v <- Set.elems new_export_vars] ++
            moduleExports mod

  in (mod {moduleExports = exports}, pre_imports, other_globals)

slurpExports' :: Set.Set Var -> Set.Set Var -> [GlobalDef]
              -> (Set.Set Var, [PreImport], [GlobalDef])
slurpExports' old_exported new_exported gdefs 
    -- If no new exported variables were added since last time, then finish
  | Set.null (new_exported Set.\\ old_exported) = (new_exported, [], gdefs)
  | otherwise =
    let -- Find the exported definitions and convert them
        (export_defs, other_defs) = partition is_exported gdefs
        imports = map mkPreImport export_defs
        
        -- Find additional definitions mentioned by these
        other_def_vars = Set.fromList $ map globalDefiniendum other_defs
        additional_exported =
          (mconcat $ map findReferencedGlobals imports) other_def_vars
        
        -- Include the additional definitions
        (final_exported, imports2, leftover) =
          slurpExports' new_exported (new_exported `Set.union` additional_exported) other_defs
    in (final_exported, imports ++ imports2, leftover)
  where
    is_exported gdef = globalDefiniendum gdef `Set.member` new_exported

mkPreImport :: GlobalDef -> PreImport
mkPreImport (GlobalFunDef (Def v f)) =
  let f_val = if shouldInline f then Just f else Nothing
      ep    = funEntryPoints f
  in Def v (PreImportFun (funType f) ep f_val)

mkPreImport (GlobalDataDef (Def v dat)) =
  Def v (PreImportData dat)
  
-------------------------------------------------------------------------------
-- Finding global variable references

-- | The variables in a global definition that may be referenced by another
--   module.  These variables include entry points because closure conversion 
--   may insert references to entry points.
importReferenceableVars :: Import -> [Var]
importReferenceableVars (ImportClosureFun ep _) = entryPointsVars ep
importReferenceableVars (ImportPrimFun v _ _) = [v]
importReferenceableVars (ImportData v _) = [v]

importListReferenceableVars :: [Import] -> [Var]
importListReferenceableVars = concatMap importReferenceableVars

-- | The variables that are defined by a module and may be referenced
--   by another module.  These variables include entry points because
--   closure conversion may insert references to entry points. This
--   function doesn't transitively find references that may appear
--   after inlining a global entity's definition into another module.
moduleExportReferenceableVars :: Module -> [Var]
moduleExportReferenceableVars mod =
  let exported_vars = [v | (v, _) <- moduleExports mod]
      defs = concatMap groupMembers $ moduleGlobals mod

      -- Get a list including 'v' and its entry points (if any)
      with_entry_points v =
        case find ((v ==) . globalDefiniendum) defs
        of Just (GlobalFunDef (Def _ fun)) ->
             case funEntryPoints fun
             of Just ep -> entryPointsVars ep
                Nothing -> [v]
           Just (GlobalDataDef (Def _ _)) ->
             [v]
           Nothing ->
             internalError "moduleReferenceableVars"
  in concatMap with_entry_points exported_vars

-- | Given a set of global variables in the current module,
--   get the subset that is referenced by something.
type FindRefs = Set.Set Var -> Set.Set Var

findRefsMaybe f Nothing  s = s
findRefsMaybe f (Just x) s = f x s

findReferencedGlobals :: PreImport -> FindRefs
findReferencedGlobals (Def _ (PreImportFun _ m_ep m_f)) =
  findRefsMaybe findRefsEntryPoints m_ep `mappend`
  findRefsMaybe findRefsFun m_f

findReferencedGlobals (Def _ (PreImportData (StaticData val))) =
  findRefsVal val

findRefsEntryPoints :: EntryPoints -> FindRefs
findRefsEntryPoints ep = mconcat $ map findRefVar $ entryPointsVars ep

findRefVar v dom = if v `Set.member` dom then Set.singleton v else mempty

findRefsVal value =
  case value
  of VarV v -> findRefVar v
     RecV _ vs -> findRefsVals vs
     LitV _ -> mempty

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
       mconcat (findRefsStm body : map (findRefsFun . definiens) (groupMembers defs))
     SwitchE v alts ->
       mconcat (findRefsVal v : map (findRefsStm . snd) alts)
     ReturnE atom -> findRefsAtom atom

findRefsFun f = findRefsStm (funBody f) `mappend`
                findRefsMaybe findRefsEntryPoints (funEntryPoints f)

-------------------------------------------------------------------------------
-- Loading an interface

-- | Add an interface to a module's import set.  Variable IDs are not
--   necessarily unique between the module and interface.  Variables are
--   renamed so that distinct variables have distinct IDs, and so that
--   variables having the same label will be renamed to have the same ID.
--   The interface will be added to the module's import list.
--
--   The module being updated should have gone through record flattening, 
--   and should not have gone through closure conversion.
addInterfaceToModuleImports :: Interface -> Module -> IO Module
addInterfaceToModuleImports iface mod = do
  -- Rename all variables in the interface to avoid variable ID collisions
  rn_iface <-
    withTheLLVarIdentSupply $ \id_supply -> runFreshVarM id_supply $ do
      freshenInterface iface

  -- Identify variables defined in 'iface' and defined in 'mod'
  let iface_export_vars = importListReferenceableVars $ ifaceExports rn_iface
  let module_import_vars = importListReferenceableVars $ moduleImports mod
  let module_export_vars = moduleExportReferenceableVars mod

  -- The set of all variables that the interface may share with
  -- the builtins and/or the module.  This set includes variables that
  -- may be created later by closure conversion.
  --
  -- Duplicate list entries are eliminated by creating a set.
  let visible_variables =
        let vs = 
              -- Order is important.  From last to first,
              -- builtin variable IDs override
              -- the module's variable IDs, and either of these
              -- overrides the interface's variable IDs.
              importListReferenceableVars (ifaceImports rn_iface) ++
              iface_export_vars ++
              module_import_vars ++
              module_export_vars ++
              allBuiltins
        in labelMap vs

  -- Get 'LabelMap's of the exported variables
  let iface_exports = labelMapRestriction visible_variables iface_export_vars
  let mod_imports = labelMapRestriction visible_variables module_import_vars
  let mod_exports = labelMapRestriction visible_variables module_export_vars

  -- No variable may be defined by both the interface and the module
  unless (Map.null $ iface_exports `Map.intersection` mod_exports) $
    fail "Found a duplicate variable definition when loading a module interface"

  -- Remove duplicate definitions.
  -- Remove imports from the interface that are defined or imported by the 
  -- module.  Remove imports from the module that are defined by the
  -- interface.
  let filtered_iface = filterInterface mod_imports mod_exports rn_iface
  let filtered_mod = filterModule iface_exports mod

  -- Rename variables in the interface
  (rn_imports, rn_exports, interface_renaming) <-
    withTheLLVarIdentSupply $ \id_supply -> runFreshVarM id_supply $ do
      renameInterface visible_variables filtered_iface

  -- DEBUG
  when False $ do
    putStrLn "Renamed interface"
    putStrLn "** imports"
    print $ map importVar (ifaceImports filtered_iface)
    putStrLn "** exports"
    print $ map importVar (ifaceExports filtered_iface)
    putStrLn "** all visible variables"
    putStrLn $ intercalate ", " $ map showLabel $ Map.keys visible_variables
    putStrLn "** renaming"
    print interface_renaming

  -- Insert the interface's symbols into the module's imports
  let mod' = filtered_mod {moduleImports = rn_imports ++ rn_exports ++
                                           moduleImports filtered_mod}

  -- Sanity check: the module's imports should not overlap with the
  -- filtered interface
  checkRenamedInterfaceCollisions
    (rn_imports ++ rn_exports) (moduleImports filtered_mod)

  return mod'

-- | Verify that no variable is defined by both sets of imports.
--   This should always pass, as a consequence of earlier checks.
checkRenamedInterfaceCollisions interface_imports module_imports =
  let i_vars = importListReferenceableVars interface_imports
      m_vars = importListReferenceableVars module_imports
      intersection = Set.fromList i_vars `Set.intersection` Set.fromList m_vars
  in if Set.null intersection
     then return ()
     else traceShow intersection $ internalError "checkRenamedInterfaceCollisions"
  
-- | Remove imports from the interface if they define any variables with
--   the same label as a variable that's in the list.
--   Verify that the exports don't define any such variables.
filterInterface :: LabelMap -> LabelMap -> Interface -> Interface
filterInterface other_imports other_exports (Interface imports exports) =
  Interface (filter_imports imports) (check_exports exports)
  where
    filter_imports xs = filter unique xs
      where
      unique i =
        -- Only check the import's defined variable.
        -- We don't need to check for other referenceable variables, since 
        -- they won't actually be used until closure conversion occurs
        other_imports `labelMapDoesn'tContain` importVar i &&
        other_exports `labelMapDoesn'tContain` importVar i

    check_exports xs =
      if any (any (labelMapContains other_exports) . importReferenceableVars) xs
      then internalError "filterInterface: Redefined variable"
      else xs

-- | Remove imports from the module if they define a variable found in
--   the list.
filterModule :: LabelMap -> Module -> Module
filterModule label_map mod =
  mod {moduleImports = filter_imports $ moduleImports mod}
  where
    filter_imports xs =
      filter (labelMapDoesn'tContain label_map . importVar) xs

-- | Remove all imports of variables from a module if the variable is 
--   defined in the module.
--
--   This function is called immediately after parsing low-level modules.
--   As an artifact of the parser, a module can import a variable that
--   it defines.  Such imports are superfluous.
removeSelfImports :: Module -> IO Module
removeSelfImports mod =
  let exp_vars = moduleExportReferenceableVars mod
      exp_var_map = labelMap exp_vars
  in return $ filterModule exp_var_map mod

-- | Rename all variables in an interface.  This is done after an interface
--   is loaded to eliminate ID collisions.
freshenInterface :: Interface -> FreshVarM Interface
freshenInterface iface = do
  -- Get all external variables in the interface.  Remove duplicates.
  let iface_extern_variables =
        let imp_vars = importListReferenceableVars $ ifaceImports iface
            exp_vars = importListReferenceableVars $ ifaceExports iface
        in imp_vars ++ (exp_vars \\ imp_vars)

  -- Rename each of these variables
  renamed_vars <- mapM newClonedVar iface_extern_variables

  -- Construct a renaming
  let renaming = mkRenaming $ zip iface_extern_variables renamed_vars

  -- Rename the interface
  new_imports <- mapM (rename_import renaming) $ ifaceImports iface
  new_exports <- mapM (rename_import renaming) $ ifaceExports iface
  return $ Interface new_imports new_exports
  where
    -- Rename within an imported module
    rename_import renaming impent
      -- Error if the imported entity isn't being renamed
      | Nothing <- getRenamedVar (importVar impent) renaming =
          internalError "freshenInterface"
      | otherwise =
           renameImport RenameEverything renaming impent

-- | Rename an interface's imported and exported symbols, given the set of
--   variables that the interface's symbols should be renamed to.
--   The renaming that was applied to the interface is returned.
--
--   Exported symbols are renamed to one of the given variables, if one has
--   the same label, or else to a new variable name.
--
--   Imported symbols are discarded if the variable name is found in the 
--   list of renamed variables.  Otherwise they are renamed to a new variable
--   name.
renameInterface :: LabelMap     -- ^ The varible renaming to perform
                -> Interface    -- ^ Interface that should be renamed
                -> FreshVarM ([Import], [Import], Renaming)
                -- ^ Computes the new imports and exports
renameInterface visible_variables iface = do
  -- Get all external variables in the interface.  Remove duplicates.
  let iface_extern_variables =
        let imp_vars = importListReferenceableVars $ ifaceImports iface
            exp_vars = importListReferenceableVars $ ifaceExports iface
        in imp_vars ++ (exp_vars \\ imp_vars)

  -- Create a renaming for these variables
  new_e_vars <- mapM (renameExternallyVisibleVar visible_variables)
                iface_extern_variables
  let renaming = mkRenaming $ zip iface_extern_variables new_e_vars

  -- Apply renaming
  new_imports <- mapM (rename_import renaming) $ ifaceImports iface
  new_exports <- mapM (rename_import renaming) $ ifaceExports iface
  return (new_imports, new_exports, renaming)
  where
    -- Rename within an imported module
    rename_import renaming impent
      -- Error if the imported entity isn't being renamed
      | Nothing <- getRenamedVar (importVar impent) renaming =
          internalError "renameInterface"
      | otherwise =
           renameImport RenameNothing renaming impent
         
renameVarSet :: Renaming -> Set.Set Var -> Set.Set Var
renameVarSet rn s = Set.fromList $ map (renameVar rn) $ Set.toList s