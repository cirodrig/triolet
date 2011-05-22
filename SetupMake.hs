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
import Distribution.Simple.Compiler
import Distribution.Simple.GHC
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.PackageIndex
import Distribution.Simple.Program
import Distribution.Simple.Utils
import Distribution.Text
import Distribution.Verbosity

import SetupConfig
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
  { makeTargets :: [String]
  , makePrerequisites :: [String]
  , makeCommands :: String
  }

makeTarget rule =
  let [tgt] = makeTargets rule
  in tgt

-- | Emit a 'MakeRule' in Makefile format
formatMakeRule :: MakeRule -> String
formatMakeRule rule =
  let criterion =
        concat (intersperse " " $ makeTargets rule) ++ " : " ++
        concat (intersperse " " $ makePrerequisites rule)
      command = unlines $ map ('\t':) $ lines $ makeCommands rule
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
  in MakeRule [o_file] [src_file] $
     "mkdir -p " ++ takeDirectory o_file ++ "\n\
     \$(HC) -c $< $(PYON_HS_C_OPTS)\n\
     \touch " ++ hi_file

-- Compile with profiling
pyonHsProfFileTemplate :: MakeRuleTemplate
pyonHsProfFileTemplate build_path src_path file =
  let src_file = src_path </> file `replaceExtension` ".hs"
      o_file = build_path </> file `replaceExtension` ".p_o"
      hi_file = build_path </> file `replaceExtension` ".p_hi"
  in MakeRule [o_file] [src_file] $
     "mkdir -p " ++ takeDirectory o_file ++ "\n\
     \$(HC) -c $< $(PYON_HS_PC_OPTS)\n\
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
  in MakeRule [o_file] [src_file] $
     "mkdir -p " ++ takeDirectory o_file ++ "\n\
     \$(HC) -c $< $(PYON_HS_C_OPTS)\n\
     \touch " ++ hi_file

compileHsProfBootFile :: MakeRuleTemplate
compileHsProfBootFile build_path src_path file =
  let src_file = src_path </> file `replaceExtension` ".hs-boot"
      o_file = build_path </> file `replaceExtension` ".p_o-boot"
      hi_file = build_path </> file `replaceExtension` ".p_hi-boot"
  in MakeRule [o_file] [src_file] $
     "mkdir -p " ++ takeDirectory o_file ++ "\n\
     \$(HC) -c $< $(PYON_HS_PC_OPTS)\n\
     \touch " ++ hi_file

-- | Generate a rule to compile a C file for the RTS
compileCRtsFile :: MakeRuleTemplate
compileCRtsFile build_path source_path src =
  let o_file = build_path </> src `replaceExtension` ".o"
      i_file = source_path </> src `replaceExtension` ".c"
  in MakeRule [o_file] [i_file, "bootstrap_data"] $
     "mkdir -p " ++ takeDirectory o_file ++ "\n\
     \$(CC) $(RTS_C_C_OPTS) -c $< -o $@"

-- | Generate a rule to compile a C file for the RTS
compileCxxRtsFile :: MakeRuleTemplate
compileCxxRtsFile build_path source_path src =
  let o_file = build_path </> src `replaceExtension` ".o"
      i_file = source_path </> src `replaceExtension` ".cc"
  in MakeRule [o_file] [i_file, "bootstrap_data"] $
     "mkdir -p " ++ takeDirectory o_file ++ "\n\
     \$(CXX) $(RTS_CXX_C_OPTS) -c $< -o $@"

-- | Generate a rule to compile a low-level pyon file for the RTS
--
-- > build_path/A.o : src_path/A.pyasm bootstrap_data
-- > 	mkdir -p build_path
-- > 	pyon_program -B build_path/data $< -o $@
compilePyAsmRtsFile :: ExtraConfigFlags -> FilePath -> FilePath -> MakeRuleTemplate
compilePyAsmRtsFile econfig pyon_program data_path build_path source_path src =
  let o_file = build_path </> src `replaceExtension` ".o"
      iface_file = build_path </> src `replaceExtension` ".pi"
      i_file = source_path </> src `replaceExtension` ".pyasm"
  in MakeRule [o_file, iface_file] [i_file, "bootstrap_data"] $
     "mkdir -p " ++ takeDirectory o_file ++ "\n" ++
     pyon_program ++ " -B " ++ data_path ++
     " $(RTS_PYASM_C_OPTS) --keep-c-files $< -o " ++ o_file

-- | Copy a file
copyDataFile :: MakeRuleTemplate
copyDataFile build_path source_path src =
  let o_file = build_path </> src
      i_file = source_path </> src
  in MakeRule [o_file] [i_file] $
     "mkdir -p " ++ takeDirectory o_file ++ "\n\
     \cp $< $@"
      
-------------------------------------------------------------------------------
-- Command-line options used in makefiles

{-
-- | If we are using 32-bit GHC on a 64-bit system, then we need to force
--   32-bit mode when linking pyon
force32BitCompilation :: Bool
force32BitCompilation =
  case (System.Info.arch, System.Info.os)
  of ("i386", _)          -> True
     ("x86_64", "darwin") -> True
     ("x86_64", "linux")  -> False
     _                    -> error "Unrecognized host architecture"
-}
      
findExeConfig exe lbi =
  case find ((exeName exe ==) . fst) $ executableConfigs lbi
  of Just x  -> snd x
     Nothing -> error "Configuration error: Missing list of package dependences"

-- | Get flags to use for package dependences.
packageFlags exe lbi = "-hide-all-packages" :
  concat [["-package", show $ disp package_id]
         | (_, package_id) <- componentPackageDeps $ findExeConfig exe lbi]

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
  ["-X" ++ show ext | ext <- defaultExtensions $ buildInfo exe]

pyonGhcPathFlags exe lbi = o_flags ++ i_flags
  where
    o_flags = ["-outputdir", pyonBuildDir lbi]
    i_flags = ["-i" ++ path | path <- pyonBuildDir lbi : pyonSearchPaths lbi exe]

-- | Target-specific compilation flags for C, C++, and pyasm code. 
targetCompileFlags econfig = target_paths ++ target_tbb
  where
    target_paths =
      ["-I" ++ path | path <- configTargetIncludeDirs econfig]

    target_tbb =
      if configTBB econfig
      then ["-DUSE_TBB"]   
      else []

-- | Flags for compiling RTS C/C++ files
rtsCCompileFlags is_cxx lbi econfig =
  cc_warning_flags ++ dynamic_flags ++ rts_include_paths ++
  targetCompileFlags econfig
  where
    dynamic_flags = ["-fPIC"]   -- Position-independent code

    rts_include_paths = ["-I" ++ path | path <- rtsSearchPaths lbi]

    cc_warning_flags =
      -- In C, these flags turn some C warnings into errors.
      -- In C++, they're errors by default.
      if is_cxx
      then []
      else ["-Werror", "-Wimplicit-function-declaration", "-Wimplicit-int"]

-- | Flags for compiling pyasm files.
rtsPyasmCompileFlags lbi econfig = rts_include_paths ++ rts_tbb
  where
    rts_include_paths = ["-I" ++ path | path <- rtsSearchPaths lbi]
    
    rts_tbb =
      if configTBB econfig
      then ["-DUSE_TBB"]   
      else []

{-
targetCompileDefines = word_size ++ arch
  where
    arch =
      case System.Info.arch
      of "i386" -> ["-DARCH_I386"]
         "x86_64" -> ["-DARCH_X86_64"]
         _ -> error "Unrecognized architecture"
    word_size =
      case System.Info.arch
      of "i386" -> ["-DWORD_SIZE=4"]
         "x86_64" -> ["-DWORD_SIZE=8"]
         _ -> error "Unrecognized architecture"-}

targetLinkFlags econfig = target_paths
  where
    target_paths =
      ["-L" ++ path | path <- configTargetLibDirs econfig ++
                              configCxxLibDirs econfig]

targetLibs econfig = target_tbb ++ ["-lgc", "-lc", "-lm", "-lstdc++"]
  where
    target_tbb =
      if configTBB econfig
      then ["-ltbb"]
      else []

optimizationFlags lbi = prof_flag ++ opt_flag ++ suffixes
  where
    -- If compiling with profiling, use different filename suffixes
    suffixes =
      if withProfExe lbi
      then ["-osuf", "p_o", "-hisuf", "p_hi"]
      else []
    prof_flag =
      if withProfExe lbi then ["-prof"] else []
    opt_flag =
      case withOptimization lbi
      of NoOptimisation -> ["-O0"]
         _ -> ["-O"]

-- | Extra GHC flags used when profiling
profFlags = ["-prof", "-osuf", "p_o", "-hisuf", "p_hi"]

-- | Get the extra GHC command-line parameters that were specified 
--   in the build configuration
configuredGhcFlags exe lbi =
  let compiler_flavor = compilerFlavor $ compiler lbi
  in fromMaybe [] $ lookup compiler_flavor $ options (buildInfo exe)

-- | Get the options to pass to GHC for compiling a HS file that is part of
--   the Pyon executable.
pyonGhcOpts econfig exe lbi =
  let clbi = case lookup "pyon" $ executableConfigs lbi
             of Nothing -> error "Unexpected missing build info"
                Just x -> x
      options =
        ghcOptions lbi (buildInfo exe) clbi "dist/build/pyon"
      prof_options = options ++ profFlags
  in if withProfExe lbi
     then prof_options
     else options
  {-
  configuredGhcFlags exe lbi ++
  optimizationFlags lbi ++
  pyonGhcPathFlags exe lbi ++
  packageFlags exe lbi ++
  pyonExtensionFlags exe -}

-- | Get the options for linking the \'pyon\' binary.
pyonLinkOpts econfig exe lbi = ["-rtsopts"] ++ pyonGhcOpts econfig exe lbi

-------------------------------------------------------------------------------
-- Rules to generate a makefile

generateCabalMakefile verbosity econfig exe lbi = do
  (pyon_rules, pyon_object_files, pyon_source_files) <-
    generatePyonRules verbosity lbi exe
  (rts_rules, rts_files) <- generateRtsRules verbosity econfig lbi
  (data_rules, prebuilt_data_files) <- generateDataRules verbosity lbi
  test_rules <- generateTestRules verbosity lbi
  variables <- generateVariables econfig exe lbi pyon_rules rts_rules data_rules
               pyon_object_files pyon_source_files
               prebuilt_data_files
  writeCabalMakefile variables (pyon_rules ++ rts_rules ++ data_rules ++ test_rules)

-- | Create variables for a makefile.
generateVariables :: ExtraConfigFlags
                  -> Executable
                  -> LocalBuildInfo
                  -> [MakeRule]
                  -> [MakeRule]
                  -> [MakeRule]
                  -> [FilePath]
                  -> [FilePath]
                  -> [FilePath]
                  -> IO [(String, String)]
generateVariables econfig exe lbi pyon_rules rts_rules data_rules 
                  pyon_object_files pyon_source_files prebuilt_data_files = do
  -- Get paths
  cc_path <-
    case lookupProgram gccProgram $ withPrograms lbi
    of Just pgm -> return $ programPath pgm
       Nothing -> die "Cannot find 'gcc'"
  cxx_path <-
    case lookupProgram (simpleProgram "g++") $ withPrograms lbi
    of Just pgm -> return $ programPath pgm
       Nothing -> die "Cannot find 'g++'"
  hc_path <- 
    case lookupProgram ghcProgram $ withPrograms lbi
    of Just pgm -> return $ programPath pgm
       Nothing -> die "Cannot find 'ghc'"
  
  -- Linker commands
  linkshared <-
    case System.Info.os
    of "darwin" -> return "libtool -dynamic"
       "linux"  -> return "gcc -shared"
       _ -> die "Unrecognized operating system"

  -- Compute file lists
  let rts_source_files = getSources rts_rules
      rts_object_files = getObjectTargets rts_rules
      rts_interface_files = getInterfaceTargets rts_rules
      interface_data_files =
        [ dataBuildDir lbi </> "interfaces" </> fl `replaceExtension` ".pi"
        | fl <- rtsPyAsmFiles]

  return [ -- paths within the project directory
           ("BUILDDIR", buildDir lbi)
         , ("DATADIR", "data")
         , ("SRCDIR", "src")
         , ("PYON_BUILD_DIR", pyonBuildDir lbi)
         , ("RTS_BUILD_DIR", rtsBuildDir lbi)
         , ("DATA_BUILD_DIR", dataBuildDir lbi)
           -- paths outside the project directory
         , ("INCLUDEDIRS", "")
         , ("LIBDIRS", "")
         , ("LIBS", "")
         , ("TARGET_LIBS", intercalate " " $ targetLibs econfig)

           -- executables
         , ("CC", cc_path)
         , ("CXX", cxx_path)
         , ("HC", hc_path)
         , ("LINKSHARED", linkshared)

           -- flags: RTS
         -- , ("CCFLAGS", intercalate " " (cc_32b_flag ++ cc_warning_flags))
         , ("RTS_C_C_OPTS", intercalate " " (rtsCCompileFlags False lbi econfig))
         -- , ("CXXFLAGS", intercalate " " cc_32b_flag)
         , ("RTS_CXX_C_OPTS", intercalate " " (rtsCCompileFlags True lbi econfig))
         -- , ("LFLAGS", intercalate " " (targetLdLinkFlags econfig))
         , ("RTS_PYASM_C_OPTS", intercalate " " (rtsPyasmCompileFlags lbi econfig))
         , ("RTS_LINK_OPTS", intercalate " " (targetLinkFlags econfig))
           -- flags: pyon program
         , ("PYON_HS_C_OPTS", intercalate " " $ pyonGhcOpts econfig exe (lbi {withProfExe = False}))
         , ("PYON_HS_PC_OPTS", intercalate " " $ pyonGhcOpts econfig exe (lbi {withProfExe = True}))
         , ("PYON_L_OPTS", intercalate " " $ pyonLinkOpts econfig exe lbi)

           -- files: RTS
         , ("RTS_SOURCE_FILES", makefileList rts_source_files)
         , ("RTS_OBJECT_FILES", makefileList rts_object_files)
         , ("RTS_INTERFACE_FILES", makefileList rts_interface_files)
           -- files: pyon program
         , ("PYON_SOURCE_FILES", makefileList pyon_source_files)
         , ("PYON_OBJECT_FILES", makefileList pyon_object_files)
           -- files: pyon data files
         , ("BOOT_DATA_FILES", makefileList prebuilt_data_files)
         , ("INTERFACE_DATA_FILES", makefileList interface_data_files)
         ]
  where
    makefileList ss = concat $ intersperse " " ss
    getSources rules = filter is_source $ concatMap makePrerequisites rules
      where
        is_source f = takeExtension f `elem` [".hs", ".c", ".pyasm"]
    getObjectTargets rules = 
        filter ((".o" ==) . takeExtension) $ concatMap makeTargets rules
    getInterfaceTargets rules = 
        filter ((".pi" ==) . takeExtension) $ concatMap makeTargets rules

-- | Create Makefile rules to create all object files used in building the
-- 'pyon' executable.
--
--   Returns the rules, the set of object files, and the set of source files.
generatePyonRules :: Verbosity
                  -> LocalBuildInfo
                  -> Executable
                  -> IO ([MakeRule], [FilePath], [FilePath])
generatePyonRules verb lbi exe = do
  info verb "Locating source code files for 'pyon'"
  hs_rules <- generateBuildRules pyonHsFileTemplate pyon_build_dir
              pyon_source_paths pyon_modules
  hs_p_rules <- generateBuildRules pyonHsProfFileTemplate pyon_build_dir
                pyon_source_paths pyon_modules
  boot_rules <- generateBuildRulesWhenFound compileHsBootFile pyon_build_dir
                pyon_source_paths boot_modules
  boot_p_rules <- generateBuildRulesWhenFound compileHsProfBootFile pyon_build_dir
                  pyon_source_paths boot_modules

  let rules = hs_rules ++ hs_p_rules ++ boot_rules ++ boot_p_rules
      -- The profiling and non-profiling rules have the same sources, so
      -- just look at the non-profiling rules.
      source_files = concatMap makePrerequisites (hs_rules ++ boot_rules)
      
      -- The object files depend on whether we're doing profiling.
      -- Ignore o-boot files, they are not real object files.
      object_files =
        if withProfExe lbi
        then filter ((".p_o" `isPrefixOf`) . takeExtension) $ 
             concatMap makeTargets hs_p_rules
        else filter ((".o" `isPrefixOf`) . takeExtension) $ 
             concatMap makeTargets hs_rules
  return (rules, object_files, source_files)
  where
    pyon_build_dir = pyonBuildDir lbi
    pyon_source_paths = pyonSearchPaths lbi exe
    pyon_modules = [toFilePath m `addExtension` ".hs"
                   | m <- fromString "Main" : exeModules exe]
  
    boot_modules = [toFilePath m `addExtension` ".hs-boot"
                   | m <- fromString "Main" : exeModules exe]

-- | Create Makefile rules for all object files in the RTS.
generateRtsRules :: Verbosity -> ExtraConfigFlags -> LocalBuildInfo
                 -> IO ([MakeRule], [FilePath])
generateRtsRules verb econfig lbi = do
  info verb "Locating source code files for RTS"
  c_rules <- generateBuildRules compileCRtsFile rts_build_dir rts_source_paths
             rtsCSourceFiles
  cxx_rules <- generateBuildRules compileCxxRtsFile rts_build_dir
               rts_source_paths rtsCxxSourceFiles
  asm_rules <- generateBuildRules (compilePyAsmRtsFile econfig pyon_program data_path)
               rts_build_dir rts_source_paths rtsPyAsmFiles
  let rules = c_rules ++ cxx_rules ++ asm_rules
  return (rules, concatMap makePrerequisites rules)
  where
    pyon_program = pyonBuildDir lbi </> "pyon"
    data_path = dataBuildDir lbi
    rts_build_dir = rtsBuildDir lbi
    rts_source_paths = rtsSearchPaths lbi

-- | Create Makefile rules for data files that will be installed along with
--   the executable.  Also, return the list of data files that are _not_
--   generated by the build process.
generateDataRules :: Verbosity -> LocalBuildInfo -> IO ([MakeRule], [FilePath])
generateDataRules verb lbi = do
  info verb "Locating data files"
  
  -- Find all testcases
  pre_testcase_files <- getDirectoryContents "data/testcases"
  let testcase_files = filter ((".py" ==) . takeExtension) pre_testcase_files
      testcase_rules =
        map (copyDataFile (dataBuildDir lbi </> "testcases") "data/testcases") testcase_files
        
  -- Find all RTS interfaces
  let rts_interface_files = map (`replaceExtension` ".pi") rtsPyAsmFiles
      build_dir = rtsBuildDir lbi
      rts_interface_rules =
        map (copyDataFile (dataBuildDir lbi </> "interfaces") build_dir) rts_interface_files

  let prebuilt_data_files =
        map makeTarget $ testcase_rules ++ prebuilt_data_rules

  return (testcase_rules ++ rts_interface_rules ++ prebuilt_data_rules,
          prebuilt_data_files)
  where
    -- Copy prebuilt files from 'data' to 'dist/data'
    prebuilt_data_rules =
      [copyDataFile (dataBuildDir lbi) "data" filename
      | filename <- prebuiltDataFiles]

generateTestRules verbosity lbi = do
  -- Generate a single rule.  The first filename in the list is the main file. 
  source_files <- mapM find_file ["testdriver.hs", "TestCase.hs"]

  let rule = MakeRule [out_file] source_files $
             "mkdir -p " ++ takeDirectory out_file ++ "\n\
             \$(HC) " ++ hcflags ++ " --make $< -o $@"
  return [rule]
  where
    hcflags = intercalate " " (include_flags ++ dir_flags)
    include_flags = ["-i" ++ path | path <- search_paths]
    dir_flags = ["-outputdir", out_path]
    search_paths = testDriverSearchPaths lbi
    out_path = testDriverBuildDir lbi
    out_file = testDriverProgram lbi
    
    find_file fname = do 
      path <- findFilePath' search_paths fname
      return $ path </> fname
    
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

