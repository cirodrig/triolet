
module SetupSrc.Rules
       (generateTrioletCRules,
        generateTrioletPreprocessorRules,
        moveDataFiles,
        moveRtsDataFiles,
        compileRtsCFiles,
        compileRtsCxxFiles,
        compileRtsLltFiles,
        linkRts,
        compileTestDriver,
        generateShakeRules,
        shake,
        shakeWithRules)
where

import Control.Monad
import Control.Monad.Trans
import Data.Monoid
import Debug.Trace
import qualified Development.Shake as Shake
import qualified Distribution.Simple.Build.PathsModule
import qualified Distribution.Simple.Build.Macros
import Distribution.Simple.Program
import Distribution.PackageDescription
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.PreProcess
import Distribution.Simple.Utils
import Distribution.Verbosity
import System.Directory
import System.FilePath
import qualified System.Info

import SetupSrc.Args
import SetupSrc.Command
import SetupSrc.Config
import SetupSrc.Path

-- | Create a shake rule that exactly matches a string
(?=) :: String -> Shake.Action () -> Shake.Rules ()
s ?= r = (s ==) Shake.?> \_ -> r

-- | Create a shake rule that exactly matches either of two strings
(??=) :: (String, String) -> Shake.Action () -> Shake.Rules ()
(s1, s2) ??= r = match Shake.?>> \_ -> r
  where
    match x
      | s1 == x || s2 == x = Just [s1, s2]
      | otherwise          = Nothing

-- | The autogenerated 'Paths' module
generatePathsModule verb lbi = autogen_filename ?= do
  Shake.writeFile' autogen_filename paths_module
  where
    pkg_desc = localPkgDescr lbi
    paths_module =
      Distribution.Simple.Build.PathsModule.generate pkg_desc lbi
    autogen_filename = autogenPathsFile lbi

-- | Auto-generated files describing properties of the target architecture
generateMachineInfo verb lbi = (module_file, header_file) ??= do
  int_size <- getCSizeOf verb "int"
  ptr_size <- getCSizeOf verb "void *"

  liftIO $ createDirectoryIfMissingVerbose verb True $ dropFileName module_file
  liftIO $ createDirectoryIfMissingVerbose verb True $ dropFileName header_file
  Shake.writeFile' module_file $ module_text int_size ptr_size
  Shake.writeFile' header_file $ header_text int_size ptr_size
  where
    module_file = autogenMachineFile lbi
    header_file = autogenMachineHeaderFile lbi
    
    module_text int_size ptr_size =
      "-- Autogenerated module\n" ++
      "module Machine where\n" ++
      "targetWordSizeBytes :: Int\n" ++
      "targetWordSizeBytes = " ++ show ptr_size ++ "\n" ++
      "targetIntSizeBytes :: Int\n" ++
      "targetIntSizeBytes = " ++ show int_size ++ "\n"

    header_text int_size ptr_size =
      "#ifndef _MACHINE_H_\n" ++
      "#define _MACHINE_H_\n" ++
      "#define WORD_SIZE " ++ show ptr_size ++ "\n" ++
      "#define INT_SIZE " ++ show int_size ++ "\n" ++
      "#endif\n"

-- | Generate C headers required by 
generateCabalMacros verb lbi = dst_path ?= do
  let pkg_desc = localPkgDescr lbi
  let file_text = Distribution.Simple.Build.Macros.generate pkg_desc lbi
  Shake.writeFile' dst_path file_text
  where
    dst_path = cabalMacrosFile lbi

-- | Create a rule to compile a C source file that is part of triolet
compileCTrioletFile :: Verbosity
                    -> LocalBuildInfo
                    -> ExtraConfigFlags
                    -> FilePath        -- ^ Source file 
                    -> FilePath        -- ^ Object file
                    -> Shake.Rules ()  -- ^ Rule generator
compileCTrioletFile verb lbi econfig src_file dst_file =
  -- Run the compiler
  let exe = getTrioletExe lbi
      configured_args = trioletCcArgs econfig exe lbi
      args = ["-c", src_file, "-o", dst_file] ++ configured_args
      Just cc = lookupProgram gccProgram $ withPrograms lbi 
  in dst_file ?= do
       -- The auto-generated preprocessor macros file must exit       
       Shake.need [cabalMacrosFile lbi]
       runCommand (invokeProgram verb cc args)

-- | Create a rule to invoke GHC for the main Triolet executable.
compileTriolet :: Verbosity
               -> LocalBuildInfo
               -> ExtraConfigFlags
               -> [FilePath]    -- ^ All Haskell sources
               -> [FilePath]    -- ^ All C objects
               -> FilePath      -- ^ The 'Main' file 
               -> Shake.Rules ()
compileTriolet verb lbi econfig hs_sources c_objects main = target ?= do
  Shake.need hs_sources
  Shake.need c_objects

  -- Invoke GHC to build Triolet
  let exe = getTrioletExe lbi
  let configured_args = trioletGhcArgs econfig exe lbi
      -- Source files that GHC will compile
      source_args = main : c_objects
      args = ["--make", "-o", target] ++ source_args ++ configured_args
      Just ghc = lookupProgram ghcProgram $ withPrograms lbi 
  runCommand $ invokeProgram verb ghc args
  where
    target = trioletFile lbi
  
-- | Run a C program to find the size of a C data type
getCSizeOf :: Verbosity -> String -> Shake.Action Int
getCSizeOf verb type_name = liftIO $ do
  tmpdir <- getTemporaryDirectory
  withTempDirectory verb tmpdir "setup." $ \mydir -> do
    let src_file = mydir </> "main.c"
        exe_file = mydir </> "main"

    -- Create and run a C program to get the size
    writeFile src_file sizeof_code
    rawSystemExit verb "gcc" [src_file, "-o", exe_file]
    sizeof_string <- rawSystemStdout verb exe_file []
    size <- return $! read sizeof_string
    
    info verb $ "Calculated  sizeof(" ++ type_name ++ ") = " ++ show size
    return size
  where
    sizeof_code =
      "#include <stdio.h>\n" ++
      "int main() {\n" ++
      "  printf(\"%d\\n\", (int)sizeof(" ++ type_name ++ "));\n" ++
      "  return 0;\n" ++
      "}\n"

-------------------------------------------------------------------------------
-- Rules for building Triolet

-- | Generate rules to compile all C files that are part of triolet.
--   Return rules and a list of object files.
generateTrioletCRules :: Verbosity -> LocalBuildInfo -> ExtraConfigFlags
                      -> IO (Shake.Rules (), [FilePath])
generateTrioletCRules verb lbi econfig =
  liftM mconcat $ mapM generate_rule $ trioletCFiles lbi
  where
    search_paths = trioletSearchPaths lbi

    generate_rule c_file = do
      file_path <- findInSearchPaths search_paths c_file
      let obj_path = trioletBuildDir lbi </> (c_file `replaceExtension` ".o")

      -- Invoke C compiler
      let rule = compileCTrioletFile verb lbi econfig file_path obj_path
      return (rule, [obj_path])

-- | Find all Haskell files in Triolet that are auto-generated or preprocessed
--   and generate rules for them.
--
--   All modules are scanned.  If a preprocessor input is found for a module,
--   a rule is generated for it.
--   The rules and a list of Haskell file paths is returned.
generateTrioletPreprocessorRules :: Verbosity
                                 -> LocalBuildInfo
                                 -> IO (Shake.Rules (), [FilePath])
generateTrioletPreprocessorRules verb lbi =
  liftM mconcat $ mapM generate_rule $ trioletModulePaths lbi
  where
    generate_rule m = first_match m rules
    first_match m (r:rs) = do
      result <- r verb lbi search_paths m
      case result of
        Nothing           -> first_match m rs
        Just (rule, path) -> return (rule, [path])
    first_match m [] =
      error $ "Cannot find file or preprocessor input of " ++ (m `addExtension` ".hs")

    search_paths = trioletSearchPaths lbi

    -- Search rules.  The 'findHaskellFile' rule must be last so that
    -- preprocessor files override .hs sources.
    rules = [findAlexFile, findHappyFile, findHscFile,
             findPathsFile, findMachineFile, findHaskellFile]

findInputFile :: String
              -> (FilePath -> IO (Shake.Rules (), FilePath))
              -> SearchPaths
              -> FilePath
              -> IO (Maybe (Shake.Rules (), FilePath))
findInputFile ext action search_paths path = do
  m_result <- optFindInSearchPaths search_paths (path `addExtension` ext)
  case m_result of
    Nothing         -> return Nothing
    Just found_path -> liftM Just $ action found_path

-- | If a @.hs@ file exists, then it will be used when building
findHaskellFile _ _ search_paths path =
  findInputFile ".hs" (\p -> return (return (), p)) search_paths path

-- | Autogenerated \"Paths\" file
findPathsFile verb lbi search_paths path
  | path == autogenPathsPath lbi = do
    info verb $ "Will auto-generate " ++ (path `addExtension` ".hs")
    return $ Just (generatePathsModule verb lbi, autogenPathsFile lbi)
  | otherwise = return Nothing

-- | Autogenerated \"Machine\" file.
--   A rule is generated by 'generateMachineInfo'.  Do not generate a rule now.
findMachineFile verb lbi search_paths path
  | path == autogenMachinePath lbi = do
    info verb $ "Will auto-generate " ++ (path `addExtension` ".hs")
    return $ Just (return (), autogenMachineFile lbi)
  | otherwise = return Nothing

data Preprocessor =
  Preprocessor
  { ppExtension :: !String
  , ppReadableName :: !String
  , ppPrerequisites :: !(LocalBuildInfo -> FilePath -> [FilePath])
  , ppCabalPreprocessor :: !(BuildInfo -> LocalBuildInfo -> PreProcessor)
  }

noPrerequisites _ _ = []

-- | Attempt to generate Shake rules using the given preprocessor.
--   Search for the preprocessor's input file and generate a rule.
--
--   Return a 'Just' value on success, or 'Nothing' on failure
usePreprocessor :: Preprocessor -> Verbosity -> LocalBuildInfo -> SearchPaths
                -> FilePath -> IO (Maybe (Shake.Rules (), FilePath))
usePreprocessor pp verb lbi search_paths path =
  findInputFile ext create_rule search_paths path
  where
    ext = ppExtension pp
    dst_path = trioletBuildDir lbi </> path `addExtension` ".hs"

    -- Create a Shake rule with the given input file path
    create_rule found_path = do
      info verb $ "Will generate " ++ dst_path ++ " with " ++ ppReadableName pp
      let exe = getTrioletExe lbi
          preprocessor = ppCabalPreprocessor pp (buildInfo exe) lbi
          prerequisites = ppPrerequisites pp lbi dst_path
          rule = dst_path ?= do
            Shake.need prerequisites
            liftIO $ runSimplePreProcessor preprocessor
                     found_path dst_path verb
      return (rule, dst_path)

findAlexFile =
  usePreprocessor $ Preprocessor ".x" "Alex" noPrerequisites ppAlex

findHappyFile =
  usePreprocessor $ Preprocessor ".y" "Happy" noPrerequisites ppHappy

findHscFile =
  usePreprocessor $ Preprocessor ".hsc" "Hsc2Hs" hsc_prerequisites ppHsc2hs
  where
    hsc_prerequisites lbi _ = [cabalMacrosFile lbi]

-------------------------------------------------------------------------------
-- Rules for data files

moveDataFile lbi file_path = dst_path ?= Shake.copyFile' src_path dst_path 
  where
    dst_path = dataBuildDir lbi </> file_path
    src_path = dataSourceDir </> file_path

-- | Move data files into the build directory
moveDataFiles lbi = mconcat $ map (moveDataFile lbi) prebuiltDataFiles 

-- | Move compiled library files into the build directory
moveRtsDataFiles lbi =
  (prefix </> "*.ti") Shake.*> \dst_path -> do
    let src_file = dropPathPrefix prefix dst_path `replaceExtension` ".llt.ti"
        src_path = rtsBuildDir lbi </> src_file
    Shake.copyFile' src_path dst_path
  where
    prefix = dataBuildDir lbi </> "interfaces"

-------------------------------------------------------------------------------
-- Rules for the RTS

dropPrefix (x:xs) (y:ys) | x == y    = dropPrefix xs ys
                         | otherwise = error "Unexpected prefix"
dropPrefix [] ys = ys

dropPathPrefix pfx p = dropPrefix (addTrailingPathSeparator pfx) p

compileCRtsFile verb lbi econfig src_path obj_path =
  -- Run the compiler
  let exe = getTrioletExe lbi
      configured_args = rtsCcArgs False econfig exe lbi
      args = ["-c", src_path, "-o", obj_path] ++ configured_args

      -- We can't use 'gccProgram' here because it automatically inserts the
      -- flag -m32 if the Haskell compiler's output is 32-bit x86 code.
      -- The C compiler should generate target-compatible code. 
      Just cc = lookupProgram (simpleProgram "gcc") $ withPrograms lbi
  in runCommand (invokeString verb "gcc" args)

compileCxxRtsFile verb lbi econfig src_path obj_path =
  -- Run the compiler
  let exe = getTrioletExe lbi
      configured_args = rtsCcArgs True econfig exe lbi
      args = ["-c", src_path, "-o", obj_path] ++ configured_args
      Just cxx = lookupProgram (simpleProgram "g++") $ withPrograms lbi
  in runCommand (invokeProgram verb cxx args)

compileLltRtsFile verb lbi econfig src_path obj_path =
  let triolet = trioletFile lbi
      data_args = ["-B", dataBuildDir lbi]
      args = data_args ++ [src_path, "-o", obj_path] ++ rtsLltArgs econfig lbi
  in runCommand (invokeString verb triolet args)

needRtsHeaders lbi = do
  Shake.need [autogenMachineHeaderFile lbi]
  Shake.need [dataBuildDir lbi </> f | f <- prebuiltDataFiles]

compileRtsCFiles verb lbi econfig =
  build_dir ++ "//*.c.o" Shake.*> \obj_path -> do
    -- Remove the build directory prefix and the extension
    let file_name = dropExtension $ dropPathPrefix build_dir obj_path
        src_path = rtsSourceDir </> file_name
    needRtsHeaders lbi
    compileCRtsFile verb lbi econfig src_path obj_path
  where
    build_dir = rtsBuildDir lbi

compileRtsCxxFiles verb lbi econfig =
  build_dir ++ "//*.cc.o" Shake.*> \obj_path -> do
    -- Remove the build directory prefix and the extension
    let file_name = dropExtension $ dropPathPrefix build_dir obj_path
        src_path = rtsSourceDir </> file_name
    needRtsHeaders lbi
    compileCxxRtsFile verb lbi econfig src_path obj_path
  where
    build_dir = rtsBuildDir lbi

compileRtsLltFiles verb lbi econfig =
  target_patterns Shake.*>> \[obj_path, _] -> do
    Shake.need [trioletFile lbi] -- Need compiler
    needRtsHeaders lbi           -- Need headers

    -- Remove the build directory prefix and the extension
    let file_name = dropExtension $ dropPathPrefix build_dir obj_path
        src_path = rtsSourceDir </> file_name
    traceShow file_name $ compileLltRtsFile verb lbi econfig src_path obj_path
  where
    build_dir = rtsBuildDir lbi
    target_patterns =
      [build_dir ++ "//*.llt.o", build_dir ++ "//*.llt.ti"]

linkRts verb lbi econfig = rtsFile lbi ?= do
  Shake.need objects

  let link_flags = targetLinkFlags econfig
      args = objects ++ ["-o", rtsFile lbi] ++ link_flags
  link_shared args
  where
    objects = [rtsBuildDir lbi </> f | f <- rtsObjectFiles]
    link_shared args =
      let (prog_name, os_args) =
            case System.Info.os
            of "linux"  -> ("gcc", ["-shared"])
               "darwin" -> ("libtool", ["-dynamic"])
               _        -> error "Unrecognized operating system"
      in runCommand $ invokeString verb prog_name (os_args ++ args)

-------------------------------------------------------------------------------
-- Rules for testing

compileTestDriver verb lbi = test_file ?= do
  -- Triolet must be built first
  Shake.need [SetupSrc.Path.trioletFile lbi]
  Shake.need $ SetupSrc.Path.dataFiles lbi

  -- Find source files
  test_main_file <-
    liftIO $ findInSearchPaths testDriverSearchPaths testDriverMain
  test_src_files <-
    liftIO $ sequence [findInSearchPaths testDriverSearchPaths (f `addExtension` ".hs")
                      | f <- testDriverModules]
  Shake.need (test_main_file : test_src_files)

  -- Compile it
  let configured_args = testDriverGhcArgs lbi
      args = ["--make", test_main_file, "-o", test_file] ++ configured_args
      Just ghc = lookupProgram ghcProgram $ withPrograms lbi 
  runCommand $ invokeProgram verb ghc args
  where
    test_file = testDriverFile lbi

-------------------------------------------------------------------------------
-- Top-level stuff

-- | Define all shake rules
generateShakeRules :: Verbosity
                   -> LocalBuildInfo
                   -> ExtraConfigFlags
                   -> IO (Shake.Rules ())
generateShakeRules verb lbi econfig = do              
  -- Scan for files and configuration data
  econfig <- readExtraConfigFile
  (pp_rules, triolet_hs_files) <- generateTrioletPreprocessorRules verb lbi
  (c_rules, triolet_obj_files) <- generateTrioletCRules verb lbi econfig
  main_file <- findTrioletMainFile lbi

  return $ do
    -- Define all rules here
    SetupSrc.Rules.generateMachineInfo verb lbi
    SetupSrc.Rules.generateCabalMacros verb lbi
    SetupSrc.Rules.compileTriolet verb lbi econfig triolet_hs_files
      triolet_obj_files main_file
    pp_rules
    c_rules
    SetupSrc.Rules.moveDataFiles lbi
    SetupSrc.Rules.moveRtsDataFiles lbi
    SetupSrc.Rules.compileRtsCFiles verb lbi econfig
    SetupSrc.Rules.compileRtsCxxFiles verb lbi econfig
    SetupSrc.Rules.compileRtsLltFiles verb lbi econfig
    SetupSrc.Rules.linkRts verb lbi econfig
    SetupSrc.Rules.compileTestDriver verb lbi
    return ()

shake :: Verbosity -> Shake.Rules () -> IO ()
shake verb rules = Shake.shake opts rules
  where
    opts = Shake.shakeOptions { Shake.shakeVerbosity = shake_verbosity}
    shake_verbosity
      | verb == silent = Shake.Silent
      | verb == normal = Shake.Normal
      | verb == verbose = Shake.Loud
      | verb == deafening = Shake.Diagnostic

shakeWithRules :: Verbosity -> LocalBuildInfo -> ExtraConfigFlags
               -> Shake.Rules () -> IO ()
shakeWithRules verb lbi econfig rules = do
  base_rules <- generateShakeRules verb lbi econfig
  shake verb (base_rules >> rules)
