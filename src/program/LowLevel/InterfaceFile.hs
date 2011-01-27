{-| Interface file code.

Interface files contain information about a module's exported symbols,
including definitions of symbols that may be inlined or propagated to
users.
-}

module LowLevel.InterfaceFile
       (Interface,
        pprInterface,
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
import LowLevel.Inlining
import LowLevel.Rename
import LowLevel.Print
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
renamePreImport rn (Def v pi) = do
  pi' <- case pi
         of PreImportFun ft Nothing -> return pi
            PreImportFun ft (Just f) -> do
              f' <- renameFun RenameNothing rn f
              return $ PreImportFun ft (Just f')
            PreImportData sd -> do
              sd' <- renameStaticData RenameNothing rn sd
              return $ PreImportData sd'
  let v' = fromMaybe v $ lookupRenamedVar rn v
  return $ Def v' pi'

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
      
  -- Rename all exported variables to externally visible names
  renaming <- createExternNames (moduleModuleName mod) (moduleNameSupply mod) $
              [v | Def v _ <- pre_imports, not $ varIsExternal v]

  (renamed_mod, interface) <-
    withTheLLVarIdentSupply $ \ll_supply -> runFreshVarM ll_supply $ do
      -- Rename all uses of the exported variables.
      -- Also, rename definitions of the exported variables.
      mod1 <- renameModule RenameNothing renaming mod
      let mod2 = renameGlobalDefinitions renaming mod1
      pre_imports' <- mapM (renamePreImport renaming) pre_imports

      -- Create the interface
      exports <- mapM mkImport pre_imports'

      -- If a symbol is in the export list, it shouldn't be in the import
      -- list too.  (Really, it should be an error if a symbol is ever in
      -- both lists.)
      let imports = filter not_in_exports $
                    map clearImportDefinition $ moduleImports mod
            where
              not_in_exports impent =
                all ((importVar impent /=) . importVar) exports

      let interface = Interface { ifaceImports = imports
                                , ifaceExports = exports}
          
      -- Extend the export list with the new exported variables
      let new_exports = [(v, PyonExportSig) | Def v _ <- pre_imports'
                                            , not $ v `Set.member` export_vars]
          mod3 = mod2 {moduleExports = new_exports ++ moduleExports mod2}
      
      return (mod3, interface)

  -- DEBUG: Print the interface
  when False $ print $
    text ("Module interface of " ++ showModuleName (moduleModuleName mod)) $$
    pprInterface interface

  return (renamed_mod, interface)

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
                      return $ anonymousPyonLabel mod_name local_id Nothing
        new_v <- runFreshVarM ll_supply $ newExternalVar label (varType v)
        return (v, new_v)

-- | Replace the globally defined variables that are in the renaming.
--   All other appearances of the variables have already been renamed.
renameGlobalDefinitions renaming mod =
  mod {moduleGlobals = map rename_global_def $ moduleGlobals mod}
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

-- | Scan the given exports to select additional variables for export.
slurpExports :: Set.Set Var -> [GlobalDef] -> ([PreImport], [GlobalDef])
slurpExports exported gdefs 
  | Set.null exported = ([], gdefs)
  | otherwise =
    let -- Find the exported definitions and convert them
        (export_defs, other_defs) = partition is_exported gdefs
        imports = map mkPreImport export_defs
        
        -- Find additional definitions mentioned by these
        other_def_vars = Set.fromList $ map globalDefiniendum other_defs
        additional_exported =
          (mconcat $ map findReferencedGlobals imports) other_def_vars
        
        -- Include the additional definitions
        (imports2, leftover) = slurpExports additional_exported other_defs
    in (imports ++ imports2, leftover)
  where
    is_exported gdef = globalDefiniendum gdef `Set.member` exported

mkPreImport :: GlobalDef -> PreImport
mkPreImport (GlobalFunDef (Def v f)) =
  let f_val = if funIsInlinable f && funSmallEnoughForInlining f
              then Just f
              else Nothing
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
      extern_variables =
        Set.toList $ Set.fromList $
        allBuiltins ++ map importVar (moduleImports mod)

  -- Rename variables in the interface
  (rn_imports, rn_exports, interface_renaming) <-
    withTheLLVarIdentSupply $ \id_supply -> runFreshVarM id_supply $ do
      renameInterface extern_variables iface

  -- DEBUG
  when False $ do
    putStrLn "Renamed interface"
    putStrLn "** imports"
    print $ map importVar (ifaceImports iface)
    putStrLn "** exports"
    print $ map importVar (ifaceExports iface)
    putStrLn "** pre-existing variables"
    print extern_variables
    putStrLn "** renaming"
    print interface_renaming

  -- Insert the interface's symbols into the module's imports,
  -- replacing the existing imports.
  -- Error out if a type mismatch is detected.
  let imports = rn_imports ++ rn_exports ++
                filter not_from_interface (moduleImports mod)
        where
          not_from_interface impent =
            let v = importVar impent
            in all ((v /=) . importVar) rn_exports
      
  return $ mod {moduleImports = imports}

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
renameInterface :: [Var]        -- ^ Variables targeted by renaming
                -> Interface    -- ^ Interface that should be renamed
                -> FreshVarM ([Import], [Import], Renaming)
                -- ^ Computes the new imports and exports
renameInterface extern_variables iface = do
  -- Discard imports if the variable name is found in extern_variables.
  -- Those variables are
  -- already defined, or will be defined by another loaded interface.
  let orig_imports = filter is_not_duplicate $ ifaceImports iface
        where
          is_not_duplicate impent =
            externVarName (importVar impent) `Map.notMember` extern_variable_labels
      orig_exports = ifaceExports iface

  -- Get all external variables in the interface.  Remove duplicates. 
  let iface_extern_variables =
        let imp_vars = map importVar orig_imports
            exp_vars = map importVar orig_exports
        in imp_vars ++ (exp_vars \\ imp_vars)

  -- Create a renaming for these variables
  new_e_vars <- mapM pick_renamed_name iface_extern_variables
  let renaming = mkRenaming $ zip iface_extern_variables new_e_vars

  -- Apply renaming
  new_imports <- mapM (rename_import renaming) orig_imports
  new_exports <- mapM (rename_import renaming) orig_exports
  return (new_imports, new_exports, renaming)
  where
    -- Map from variable name to variable
    extern_variable_labels =
      Map.fromList [(externVarName v, v) | v <- extern_variables]

    externVarName v =
      case varName v
      of Just lab -> lab
         Nothing  -> internalError $ "renameInterface: " ++
                     "Imported variable has no label"

    -- Decide what to rename an external variable to.  Rename to the
    -- preexisting variable with the same name, if one exists.
    -- Otherwise create a new variable.
    pick_renamed_name interface_var
      | Just global_var <- Map.lookup lab extern_variable_labels =
          -- Rename to the preexisting variable with the same label
          return global_var
      | otherwise =
          -- Rename to a new variable with the same label
          newExternalVar lab (varType interface_var)
      where
        lab = externVarName interface_var

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
      