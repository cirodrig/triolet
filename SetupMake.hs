{-| Makefile and dependency-related functions.
-}

module SetupMake where

import Prelude hiding(catch)

import Control.Exception
import Control.Monad
import Data.List
import Data.Maybe
import System.FilePath
import System.Directory
import System.IO.Error hiding(catch)

import Distribution.ModuleName hiding(main)
import Distribution.PackageDescription
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Utils
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
  let pyon_source_files = getSources pyon_rules
      pyon_object_files = getObjectTargets pyon_rules
      rts_source_files = getSources rts_rules
      rts_object_files = getObjectTargets rts_rules
      prebuilt_data_files = map makeTarget data_rules
  return [ ("PYON_SOURCE_FILES", makefileList pyon_source_files)
         , ("PYON_OBJECT_FILES", makefileList pyon_object_files)
         , ("RTS_SOURCE_FILES", makefileList rts_source_files)
         , ("RTS_OBJECT_FILES", makefileList rts_object_files)
         , ("BOOT_DATA_FILES", makefileList prebuilt_data_files)
         , ("PYON_BUILD_DIR", pyonBuildDir lbi)
         , ("RTS_BUILD_DIR", rtsBuildDir lbi)
         , ("DATA_BUILD_DIR", dataBuildDir lbi)
         ]
  where
    makefileList ss = concat $ intersperse " " ss
    getSources rules = concatMap makePrerequisites rules
    getObjectTargets rules = 
        filter ((".o" ==) . takeExtension) $ map makeTarget rules

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

