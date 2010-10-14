{-| Makefile and dependency-related functions.
-}

module SetupMake where

import Prelude hiding(catch)

import Control.Exception
import Control.Monad
import Data.List hiding(intercalate)
import Data.Maybe
import System.FilePath
import System.Directory
import qualified System.Info
import System.IO.Error hiding(catch)

import Distribution.InstalledPackageInfo
import Distribution.ModuleName hiding(main)
import Distribution.Package
import Distribution.PackageDescription
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.PackageIndex
import Distribution.Simple.Program
import Distribution.Simple.Utils
import Distribution.Text
import Distribution.Verbosity

import SetupPaths

-- | Makefile-style dependency checking.  Return 'True' if the target is older
-- than any of the sources, or if any files do not exist.  Return 'False' if
-- the target exists and there are no sources.
olderThan :: FilePath -> [FilePath] -> IO Bool
target `olderThan` sources = do
  t_time <- getModificationTimeIfExists target
  if isNothing t_time
    then return True
    else do s_times <- mapM getModificationTimeIfExists sources
            case sequence s_times of
              Just [] -> return False
              Just s_times' -> return $ t_time < maximum s_times

getModificationTimeIfExists path = do
  liftM Just (getModificationTime path) `catch` handle_dne_error
  where
    handle_dne_error e 
      | isDoesNotExistError e = return Nothing 
      | otherwise = throw e

-- | A Makefile rule.
--
-- The strings in the rule are subject to minimal checking.  The target and
-- prerequisites may contain Makefile functions and variables, but shouldn't  
-- contain newlines, spaces, or special characters.  Newlines are permitted
-- in the command.
-- When generating a Makefile, a tab character is added to each line of the
-- command.
data MakeRule =
  MakeRule
  { makeTarget :: String
  , makePrerequisites :: [String]
  , makeCommand :: String
  }

-- | Emit a 'MakeRule' in Makefile format
formatMakeRule :: MakeRule -> String
formatMakeRule rule =
  let criterion =
        makeTarget rule ++ " : " ++
        concat (intersperse " " $ makePrerequisites rule)
      command = unlines $ map ('\t':) $ lines $ makeCommand rule
  in criterion ++ '\n' : command ++ "\n\n"

type MakeRuleTemplate = FilePath -- ^ Target directory
                     -> FilePath -- ^ Source directory
                     -> FilePath -- ^ Source file
                     -> MakeRule

findFilePath :: [FilePath]      -- ^ Search locations
             -> FilePath        -- ^ File name
             -> IO (Maybe FilePath) -- ^ Returns search location containing file
findFilePath search_paths filename =
  take_first [(doesFileExist $ path </> filename, path) | path <- search_paths]
  where
    take_first ((test, path):xs) = do
      b <- test
      if b then return (Just path) else take_first xs

    take_first [] = return Nothing

findFilePath' :: [FilePath]      -- ^ Search locations
              -> FilePath        -- ^ File name
              -> IO FilePath -- ^ Returns search location containing file
findFilePath' search_paths filename =
  maybe quit return =<< findFilePath search_paths filename
  where
    quit = do die $ "Cannot find file: " ++ filename

generateBuildRule :: MakeRuleTemplate -> FilePath -> [FilePath] -> FilePath
                  -> IO MakeRule
generateBuildRule template target_dir source_dirs source_file = do
  source_dir <- findFilePath' source_dirs source_file
  return $ template target_dir source_dir source_file

generateBuildRuleIfFound :: MakeRuleTemplate -> FilePath -> [FilePath]
                         -> FilePath -> IO (Maybe MakeRule)
generateBuildRuleIfFound template target_dir source_dirs source_file = do
  source_dir <- findFilePath source_dirs source_file
  return $ case source_dir
           of Just d  -> Just $ template target_dir d source_file
              Nothing -> Nothing

generateBuildRules :: MakeRuleTemplate -> FilePath -> [FilePath] -> [FilePath]
                   -> IO [MakeRule]
generateBuildRules template target_dir source_dirs source_files =
  mapM (generateBuildRule template target_dir source_dirs) source_files

generateBuildRulesWhenFound :: MakeRuleTemplate -> FilePath -> [FilePath]
                            -> [FilePath] -> IO [MakeRule]
generateBuildRulesWhenFound template target_dir source_dirs source_files = do
  rules <- mapM (generateBuildRuleIfFound template target_dir source_dirs)
           source_files
  return $ catMaybes rules

-------------------------------------------------------------------------------

-- | Generate a rule to compile a .hs file
--
-- > build_path/A.o : src_path/A.hs
-- > 	mkdir -p build_path
-- > 	$(HC) -c $< $(PYON_HS_C_OPTS)
-- > 	touch build_path/A.hi
pyonHsFileTemplate :: MakeRuleTemplate
pyonHsFileTemplate build_path src_path file =
  let src_file = src_path </> file `replaceExtension` ".hs"
      o_file = build_path </> file `replaceExtension` ".o"
      hi_file = build_path </> file `replaceExtension` ".hi"
  in MakeRule o_file [src_file] $
     "mkdir -p " ++ takeDirectory o_file ++ "\n\
     \$(HC) -c $< $(PYON_HS_C_OPTS)\n\
     \touch " ++ hi_file

-- | Generate a rule to compile a .hs-boot file
--
-- > build_path/A.o-boot : src_path/A.hs-boot
-- > 	mkdir -p build_path
-- > 	$(HC) -c $< $(PYON_HS_C_OPTS)
compileHsBootFile :: MakeRuleTemplate
compileHsBootFile build_path src_path file =
  let src_file = src_path </> file `replaceExtension` ".hs-boot"
      o_file = build_path </> file `replaceExtension` ".o-boot"
      hi_file = build_path </> file `replaceExtension` ".hi-boot"
  in MakeRule o_file [src_file] $
     "mkdir -p " ++ takeDirectory o_file ++ "\n\
     \$(HC) -c $< $(PYON_HS_C_OPTS)\n\
     \touch " ++ hi_file

-- | Generate a rule to compile a C file for the RTS
compileCRtsFile :: MakeRuleTemplate
compileCRtsFile build_path source_path src =
  let o_file = build_path </> src `replaceExtension` ".o"
      i_file = source_path </> src `replaceExtension` ".c"
  in MakeRule o_file [i_file, "bootstrap_data"] $
     "mkdir -p " ++ takeDirectory o_file ++ "\n\
     \$(CC) $(RTS_C_C_OPTS) -c $< -o $@"

-- | Generate a rule to compile a low-level pyon file for the RTS
--
-- > build_path/A.o : src_path/A.pyasm bootstrap_data
-- > 	mkdir -p build_path
-- > 	pyon_program -B build_path/data $< -o $@
compilePyAsmRtsFile :: FilePath -> FilePath -> MakeRuleTemplate
compilePyAsmRtsFile pyon_program data_path build_path source_path src =
  let o_file = build_path </> src `replaceExtension` ".o"
      i_file = source_path </> src `replaceExtension` ".pyasm"
  in MakeRule o_file [i_file, "bootstrap_data"] $
     "mkdir -p " ++ takeDirectory o_file ++ "\n" ++
     pyon_program ++ " -B " ++ data_path ++ " $< -o $@"

-- | Copy a file
copyDataFile :: MakeRuleTemplate
copyDataFile build_path source_path src =
  let o_file = build_path </> src
      i_file = source_path </> src
  in MakeRule o_file [i_file] $
     "mkdir -p " ++ takeDirectory o_file ++ "\n\
     \cp $< $@"
      
-------------------------------------------------------------------------------
-- Command-line options used in makefiles

data CompileMode = CompileMode | LinkMode

findExeConfig exe lbi =
  case find ((exeName exe ==) . fst) $ executableConfigs lbi
  of Just x  -> snd x
     Nothing -> error "Configuration error: Missing list of package dependences"

-- | Get flags to use for package dependences.  We exclude the 'gluon-eval'
-- package when compiling, and allow GHC to infer it, due to errors when the
-- interpreter (invoked to compile Template Haskell) tries to load C++ object
-- code.
packageFlags mode exe lbi =
  concat [["-package", show $ disp package_id]
         | (_, package_id) <-
             componentPackageDeps $ findExeConfig exe lbi,
           case mode
           of CompileMode -> pkgName package_id /= PackageName "gluon-eval"
              LinkMode -> True]

-- | Get flags for installed package documentation.  These are used to create
-- links when building the documentation.
--
-- Find Haddock interface file locations for each package.  Verify that each
-- interface file exists, then add the path as a command line parameter.
packageDocFlags exe lbi = do
  interfaces <- filterM interface_exists haddock_interfaces
  return ["--read-interface=" ++ dir ++ "," ++ path
         | (path, dir) <- interfaces]
  where
    pkg_index = installedPkgs lbi

    interface_exists (iface_path, html_path) = do
      iface_exists <- doesFileExist iface_path
      html_exists <- doesDirectoryExist html_path
      return $ iface_exists && html_exists
    
    -- Haddock interface paths and HTML directory paths of all dependences
    haddock_interfaces =
      [ (iface_path, html_path)
      | (ipid, _)  <- componentPackageDeps $ findExeConfig exe lbi
      , pkg_info   <- maybeToList $ lookupInstalledPackageId pkg_index ipid
      , iface_path <- haddockInterfaces pkg_info
      , html_path  <- haddockHTMLs pkg_info]
    

pyonExtensionFlags exe =
  ["-X" ++ show ext | ext <- extensions $ buildInfo exe]

pyonGhcPathFlags exe lbi = o_flags ++ i_flags
  where
    o_flags = ["-outputdir", pyonBuildDir lbi]
    i_flags = ["-i" ++ path | path <- pyonBuildDir lbi : pyonSearchPaths lbi exe]

layoutGhcPathFlags exe lbi = o_flags ++ i_flags
  where
    o_flags = ["-outputdir", layoutBuildDir lbi]
    i_flags = ["-i" ++ path | path <- layoutBuildDir lbi : pyonSearchPaths lbi exe]

-- | Get the options to pass to GHC for compiling a HS file.
pyonGhcOpts exe lbi =
  pyonGhcPathFlags exe lbi ++
  packageFlags CompileMode exe lbi ++
  pyonExtensionFlags exe

-- | Get the options for linking the \'pyon\' binary.
pyonLinkOpts exe lbi =
  packageFlags LinkMode exe lbi

-- | Get the options for compiling the \'ComputeLayout\' binary.  The binary
-- is compiled and linked in one step.  It's compiled with @--make@, so
-- packages are not needed.
layoutCompileOpts exe lbi =
  layoutGhcPathFlags exe lbi ++ pyonExtensionFlags exe

-------------------------------------------------------------------------------
-- Rules to generate a makefile

generateCabalMakefile verbosity exe lbi = do
  (pyon_rules, pyon_files) <- generatePyonRules verbosity lbi exe
  (rts_rules, rts_files) <- generateRtsRules verbosity lbi
  data_rules <- generateDataRules verbosity lbi
  variables <- generateVariables exe lbi pyon_rules rts_rules data_rules
  writeCabalMakefile variables (pyon_rules ++ rts_rules ++ data_rules)

-- | Create variables for a makefile.
generateVariables :: Executable
                  -> LocalBuildInfo
                  -> [MakeRule]
                  -> [MakeRule]
                  -> [MakeRule]
                  -> IO [(String, String)]
generateVariables exe lbi pyon_rules rts_rules data_rules = do
  -- Get paths
  cc_path <-
    case lookupProgram gccProgram $ withPrograms lbi
    of Just pgm -> return $ programPath pgm
       Nothing -> die "Cannot find 'gcc'"
  hc_path <- 
    case lookupProgram ghcProgram $ withPrograms lbi
    of Just pgm -> return $ programPath pgm
       Nothing -> die "Cannot find 'ghc'"
  
  -- Force 32-bit compilation?
  (cc_32b_flag, l_32b_flag, linkshared_32b_flag) <-
    let y = (["-m32"], ["-optl-m32"], [])
        n = ([], [], [])
    in case System.Info.arch
       of "i386" -> return y
          "x86_64" -> return y
          _ -> die "Unrecognized host architecture"

  -- Compute file lists
  let pyon_source_files = getSources pyon_rules
      pyon_object_files = getObjectTargets pyon_rules
      rts_source_files = getSources rts_rules
      rts_object_files = getObjectTargets rts_rules
      prebuilt_data_files = map makeTarget data_rules

  return [ -- paths within the project directory
           ("BUILDDIR", buildDir lbi)
         , ("DATADIR", "data")
         , ("SRCDIR", "src")
           -- executables
         , ("CC", cc_path)
         , ("HC", hc_path)
         , ("LINKSHARED", "libtool -dynamic")
           -- flags
         , ("CCFLAGS", intercalate " " (cc_32b_flag ++ cc_warning_flags))
         , ("LFLAGS", intercalate " " l_32b_flag)
         , ("LINKFLAGS", intercalate " " linkshared_32b_flag)
           -- paths outside the project directory
         , ("INCLUDEDIRS", "")
         , ("LIBDIRS", "")
         , ("LIBS", "")
           -- files in the project directory
         , ("PYON_SOURCE_FILES", makefileList pyon_source_files)
         , ("PYON_OBJECT_FILES", makefileList pyon_object_files)
         , ("PYON_HS_C_OPTS", intercalate " " $ pyonGhcOpts exe lbi)
         , ("PYON_L_OPTS", intercalate " " $ pyonLinkOpts exe lbi)
         , ("LAYOUT_CL_OPTS", intercalate " " $ layoutCompileOpts exe lbi)
         , ("RTS_SOURCE_FILES", makefileList rts_source_files)
         , ("RTS_OBJECT_FILES", makefileList rts_object_files)
         , ("BOOT_DATA_FILES", makefileList prebuilt_data_files)
         , ("PYON_BUILD_DIR", pyonBuildDir lbi)
         , ("RTS_BUILD_DIR", rtsBuildDir lbi)
         , ("DATA_BUILD_DIR", dataBuildDir lbi)
         ]
  where
    makefileList ss = concat $ intersperse " " ss
    getSources rules = filter is_source $ concatMap makePrerequisites rules
      where
        is_source f = takeExtension f `elem` [".hs", ".c", ".pyasm"]
    getObjectTargets rules = 
        filter ((".o" ==) . takeExtension) $ map makeTarget rules

    cc_warning_flags = ["-Werror", "-Wimplicit-function-declaration",
                        "-Wimplicit-int"]

-- | Create Makefile rules to create all object files used in building the
-- 'pyon' executable.
generatePyonRules :: Verbosity
                  -> LocalBuildInfo
                  -> Executable
                  -> IO ([MakeRule], [FilePath])
generatePyonRules verb lbi exe = do
  info verb "Locating source code files for 'pyon'"
  hs_rules <- generateBuildRules pyonHsFileTemplate pyon_build_dir
              pyon_source_paths pyon_modules
  boot_rules <- generateBuildRulesWhenFound compileHsBootFile pyon_build_dir
                pyon_source_paths pyon_modules
  let rules = hs_rules ++ boot_rules
      source_files = concatMap makePrerequisites rules
  return (rules, source_files)
  where
    pyon_build_dir = pyonBuildDir lbi
    pyon_source_paths = pyonSearchPaths lbi exe
    pyon_modules = [toFilePath m `addExtension` ".hs"
                   | m <- fromString "Main" : exeModules exe]

-- | Create Makefile rules for all object files in the RTS.
generateRtsRules :: Verbosity -> LocalBuildInfo -> IO ([MakeRule], [FilePath])
generateRtsRules verb lbi = do
  info verb "Locating source code files for RTS"
  c_rules <- generateBuildRules compileCRtsFile rts_build_dir rts_source_paths
             rtsCSourceFiles
  asm_rules <- generateBuildRules (compilePyAsmRtsFile pyon_program data_path)
               rts_build_dir rts_source_paths rtsPyAsmFiles
  let rules = c_rules ++ asm_rules
  return (rules, concatMap makePrerequisites rules)
  where
    pyon_program = pyonBuildDir lbi </> "pyon"
    data_path = dataBuildDir lbi
    rts_build_dir = rtsBuildDir lbi
    rts_source_paths = rtsSearchPaths lbi

-- | Create Makefile rules for data files that will be installed along with
-- the executable.
generateDataRules :: Verbosity -> LocalBuildInfo -> IO [MakeRule]
generateDataRules verb lbi = do
  info verb "Locating data files"
  
  -- Find all testcases
  pre_testcase_files <- getDirectoryContents "data/testcases"
  let testcase_files = filter ((".py" ==) . takeExtension) pre_testcase_files
      testcase_rules =
        map (copyDataFile (dataBuildDir lbi </> "testcases") "data/testcases") testcase_files

  return $ testcase_rules ++ prebuilt_data_rules
  where
    -- Copy prebuilt files from 'data' to 'dist/data'
    prebuilt_data_rules =
      [copyDataFile (dataBuildDir lbi) "data" filename
      | filename <- prebuiltDataFiles]

-- Write configured variables and rules into a makefile for use by 'make'
writeCabalMakefile :: [(String, String)] -- key/value pairs
                   -> [MakeRule]
                   -> IO ()
writeCabalMakefile defs rules = writeFile cabalMakeFile text
  where
    text = "# Auto-generated by Setup.hs\n" ++
           concat ([k ++ "=" ++ protect v ++ "\n" | (k,v) <- defs]) ++
           concatMap formatMakeRule rules
      
    -- Format a string so that it will be read in by 'make' as a string.
    protect s = s

