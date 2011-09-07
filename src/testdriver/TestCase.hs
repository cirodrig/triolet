{-| Regression test cases.
-}

{-# LANGUAGE MultiParamTypeClasses, DeriveDataTypeable #-}
module TestCase where

import Prelude hiding(catch)

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans
import Control.Exception
import Data.Char
import Data.List
import Data.Typeable
import System.Exit
import System.Directory
import System.FilePath
import System.Info
import System.IO
import System.Process
import System.Posix.Env

-- | Print a command before running it
dbReadProcessWithExitCode prog args stdin = do
  when debug $ liftIO $ putStrLn $ intercalate " " (prog : args)
  readProcessWithExitCode prog args stdin
  where
    debug = False

data TesterConfig =
  TesterConfig
  { -- | Directory for temporary files
    temporaryPath :: !FilePath
    -- | Directory holding Pyon's build files
  , buildDir :: !FilePath
    -- | Platform-specific options for the C compiler
  , platformCOpts :: [String]
    -- | Platform-specific options for the linker
  , platformLinkOpts :: [String]
  }

newtype Tester a = Tester {runTester :: TesterConfig -> IO a}

-- | Run a tester.  The tester's working directory is its designated
--   temporary path.
launchTester :: TesterConfig -> Tester a -> IO a
launchTester cfg m =
  bracket getCurrentDirectory setCurrentDirectory $ \_ -> do 
    setCurrentDirectory (temporaryPath cfg)
    runTester m cfg

instance Monad Tester where
  return x = Tester $ \_ -> return x
  m >>= k = Tester $ \cfg -> do x <- runTester m cfg
                                runTester (k x) cfg

instance MonadReader TesterConfig Tester where
  ask = Tester $ \cfg -> return cfg
  local f m = Tester $ \cfg -> runTester m (f cfg)

instance MonadIO Tester where
  liftIO m = Tester $ \_ -> m

handleTester :: Exception e => (e -> Tester a) -> Tester a -> Tester a
handleTester = flip catchTester

catchTester :: Exception e => Tester a -> (e -> Tester a) -> Tester a
catchTester m handler = 
  Tester $ \cfg -> (\e -> runTester (handler e) cfg) `handle` runTester m cfg

-- | Run a command in a different directory
withDirectory :: FilePath -> Tester a -> Tester a
withDirectory path m = Tester $ \cfg ->
  bracket getCurrentDirectory setCurrentDirectory $ \_ -> do 
    setCurrentDirectory path
    runTester m cfg

-- | Run a command with an alterd environment variable
withEnv :: String -> (Maybe String -> String) -> Tester a -> Tester a
withEnv key alter_value m = Tester $ \cfg ->
  bracket get_env reset_env $ \old_value -> do
    setEnv key (alter_value old_value) True
    runTester m cfg
  where
    get_env = getEnv key
    reset_env Nothing          = unsetEnv key
    reset_env (Just old_value) = setEnv key old_value True

-- | Set up the environment so that the dynamic library loader knows where to
--   find the RTS library (libpyonrts.so)
withLdPath :: Tester a -> Tester a
withLdPath m = do
  build_dir <- asks buildDir
  let lib_path = build_dir </> "rts"
      insert_lib_path = maybe lib_path (\x -> lib_path ++ ":" ++ x)

      var_name = case os
                 of "linux" -> "LD_LIBRARY_PATH"
                    "darwin" -> "DYLD_LIBRARY_PATH"
                    _ -> error "Unrecognized OS; don't know how to set up environment"

  withEnv var_name insert_lib_path m

-------------------------------------------------------------------------------
                        
data TestCase =
  TestCase
  { testDirectory :: FilePath   -- ^ Absolute path of test case's directory
  , testConfig :: !TestConfig
  }

data TestConfig =
  TestConfig
  { synopsis :: !String
  , pyonSources :: ![FilePath]
  , llpyonSources :: ![FilePath]
  , cSources :: ![FilePath]
  , expectedResult :: !ExpectedResult
  }
  deriving(Read, Show)

testSynopsis = synopsis . testConfig

testName = takeFileName . testDirectory

testPyonSources tc = 
  [testDirectory tc </> file | file <- pyonSources $ testConfig tc]
  
testLLPyonSources tc = 
  [testDirectory tc </> file | file <- llpyonSources $ testConfig tc]

testCSources tc =
  [testDirectory tc </> file | file <- cSources $ testConfig tc]

testExpectedResult = expectedResult . testConfig

-- | Read a test case, given test case directory.
--   The information is read from a file called \"config\" in the directory.
--   If the file cannot be read, an exception is thrown.
loadTestCase :: FilePath -> IO TestCase
loadTestCase path = do
  config_text <- readFile (path </> "config")
  config <-
    case reads config_text
    of (test_case, rest):_ 
         | all isSpace rest -> return test_case
       _ -> fail $ "Malformed configuration file: " ++ (path </> "config")
  return $ TestCase path config

data ExpectedResult =
    ShouldNotCompile
  | ShouldCompile
  | ShouldRun
  | ShouldPrint String
    deriving(Read, Show)

data TestFailure =
    -- | Compilation should have failed, but it passed
    CompileErrorDetectionFailed

  | CompileFailed
    { resultMessage :: String
    }
  | RunFailed 
    { resultCode :: ExitCode
    , resultStdoutLog :: String
    , resultStderrLog :: String
    }
  | CheckFailed
    { resultExpectedOutput :: String
    , resultStdoutLog :: String
    }
    deriving(Typeable)

instance Exception TestFailure

instance Show TestFailure where
  show CompileErrorDetectionFailed =
    "Compilation should fail, but it succeeded"
         
  show (CompileFailed message) =
    "Compilation failed:\n" ++ message

  show (RunFailed code out err) =
    let show_code = show $ case code
                           of ExitSuccess -> 0
                              ExitFailure n -> n
        out_text = if null out
                   then "No output on stdout"
                   else "First few characters of stdout:\n" ++ take 160 out
        err_text = if null err 
                   then "No output on stderr"
                   else "First few characters of stderr:\n" ++ take 160 err
    in "Test program terminated with result code  " ++ show_code ++ "\n" ++
       out_text ++ "\n" ++ err_text
  
  show (CheckFailed expected output) =
    "Output does not match expected result\n" ++
    "Expected:\n" ++ expected ++
    "\nGot:\n" ++ output

data TestResult = TestFailed TestFailure | TestSucceeded

instance Show TestResult where
  show TestSucceeded = "Test passed"
  show (TestFailed f) = show f

-------------------------------------------------------------------------------

-- | Name of a compiled test case
testExecutableName = "testprogram"

-- | Run a test and determine its result.
--
--   The test is run with the given path as its working directory.
--   The working directory is cleared after finishing the test case.
runTest :: TestCase             -- ^ Test case to run
        -> Tester TestResult
runTest test_case = (return . TestFailed) `handleTester`
  case testExpectedResult test_case
  of ShouldNotCompile ->
       let compile_then_fail = do
             compile_and_link
             return (TestFailed CompileErrorDetectionFailed)

           -- If compilation failed, then the test passes
           check_exception (CompileFailed _) =
             return TestSucceeded
               
           check_exception exc = return (TestFailed exc)
       in compile_then_fail `catchTester` check_exception

     ShouldCompile -> do
       compile_and_link
       return TestSucceeded

     ShouldRun -> do
       compile_and_link
       run
       return TestSucceeded

     ShouldPrint expected_out -> do
       compile_and_link
       (out, err) <- run
       check_output expected_out out
       return TestSucceeded

  where
    compile_and_link = do
      mapM_ (compilePyonFile test_case) $ testPyonSources test_case
      mapM_ (compileLLPyonFile test_case) $ testLLPyonSources test_case
      mapM_ (compileCFile test_case) $ testCSources test_case
      linkTest test_case

    run = do
      dir <- asks temporaryPath
      let prog = dir </> testExecutableName
          
      (rc, out, err) <-
        withLdPath $ liftIO $ dbReadProcessWithExitCode prog [] ""
      case rc of
        ExitSuccess   -> liftIO $ return (out, err)
        ExitFailure _ -> liftIO $ throwIO $
                         RunFailed { resultCode = rc 
                                   , resultStdoutLog = out
                                   , resultStderrLog = err}

    check_output expected_out out =
      if expected_out /= out
      then liftIO $ throwIO $ CheckFailed expected_out out
      else return ()

-- | Attempt to do a step of compilation.  If the command fails, then return
-- an error message.
runCompileCommand fail_message program opts stdin = do
  (rc, _, err) <- liftIO $ dbReadProcessWithExitCode program opts stdin
  when (rc /= ExitSuccess) $
    liftIO $ throwIO $ CompileFailed (fail_message err)

-- | Compile a file using the 'pyon' compiler.  Used for both pyon and
--   llpyon code.
compileUsingPyonCompiler fail_message compile_flags = do
  build_dir <- asks buildDir
  let pyon_program_path = build_dir </> "pyon" </> "pyon"
      build_data_path = build_dir </> "data"
      flags = ["-B", build_data_path] -- Link to the local library files
              ++ compile_flags

  runCompileCommand fail_message pyon_program_path flags ""

compilePyonFile test_case file_path = do
  test_path <- asks temporaryPath
  let obj_path = test_path </> takeFileName file_path `replaceExtension` ".o"
      flags = ["-x", "pyon",    -- Compile in pyon mode
               file_path, "-o", obj_path]
      fail_message err = "File: " ++ file_path ++ "\n" ++ err

  compileUsingPyonCompiler fail_message flags

compileLLPyonFile test_case file_path = do
  test_path <- asks temporaryPath
  let obj_path = test_path </> takeFileName file_path `replaceExtension` ".o"
      flags = ["-x", "pyonasm",    -- Compile in low-level pyon mode
               file_path, "-o", obj_path]
      fail_message err = "File: " ++ file_path ++ "\n" ++ err

  compileUsingPyonCompiler fail_message flags

compileCFile test_case file_path = do
  build_dir <- asks buildDir
  test_path <- asks temporaryPath
  platform_opts <- asks platformCOpts
  let obj_path = test_path </> takeFileName file_path `replaceExtension` ".o"
      opts = platform_opts ++
             ["-I", test_path,   -- Include files in the output directory
              "-I", build_dir </> "data" </> "include", -- Pyon library
              "-c", file_path,
              "-o", obj_path]
      fail_message err = "File: " ++ file_path ++ "\n" ++ err
  
  runCompileCommand fail_message "gcc" opts ""

linkTest test_case = do
  test_path <- asks temporaryPath
  build_dir <- asks buildDir
  platform_opts <- asks platformLinkOpts
  let c_file_paths = [test_path </> takeFileName file `replaceExtension` ".o"
                     | file <- testCSources test_case]
      llpyon_file_paths = [test_path </> takeFileName file `replaceExtension` ".o"
                        | file <- testLLPyonSources test_case]
      pyon_file_paths = [test_path </> takeFileName file `replaceExtension` ".o"
                        | file <- testPyonSources test_case]
      link_opts = platform_opts ++ 
                  ["-o", testExecutableName] ++
                  c_file_paths ++ llpyon_file_paths ++ pyon_file_paths ++
                  ["-L" ++ build_dir </> "rts",
                   "-lpyonrts", "-lgc", "-lm"]
      fail_message err = err

  runCompileCommand fail_message "gcc" link_opts ""
