{-| Regression test cases.
-}

{-# LANGUAGE MultiParamTypeClasses, DeriveDataTypeable #-}
module TestCase(TestSpec, mkSourceTest, SourceTest,
                loadTestSpec, runSourceTest)
where

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

import Statistics

-- | Print a command before running it
dbReadProcessWithExitCode prog args stdin = do
  when debug $ liftIO $ putStrLn $ intercalate " " (prog : args)
  readProcessWithExitCode prog args stdin
  where
    debug = False

-------------------------------------------------------------------------------

-- | A specification of a test case
data TestSpec =
  TestSpec
  { testDirectory :: FilePath   -- ^ Absolute path of test case's directory
  , testConfig :: !TestConfig
  }

-- | The contents of a configuration file.  This data is part of the 
--   specification of a test case.
data TestConfig =
  TestConfig
  { synopsis :: !String
  , trioletSources :: ![FilePath]
  , lltrioletSources :: ![FilePath]
  , cSources :: ![FilePath]
  , cxxSources :: ![FilePath]
  , expectedResult :: !ExpectedResult
  }
  deriving(Read, Show)

testSynopsis = synopsis . testConfig

testConfigName = takeFileName . testDirectory

testTrioletSources tc = 
  [testDirectory tc </> file | file <- trioletSources $ testConfig tc]
  
testLLTrioletSources tc =
  [testDirectory tc </> file | file <- lltrioletSources $ testConfig tc]

testCSources tc =
  [testDirectory tc </> file | file <- cSources $ testConfig tc]

testCxxSources tc =
  [testDirectory tc </> file | file <- cxxSources $ testConfig tc]

testExpectedResult = expectedResult . testConfig

mkSourceTest :: TestSpec -> TesterConfig -> SourceTest
mkSourceTest = SourceTest

-- | A testable test
data SourceTest = SourceTest TestSpec TesterConfig

instance Testable SourceTest where
  testName (SourceTest spec _) = testConfigName spec
  runTest st = runSourceTest st

-------------------------------------------------------------------------------

newtype Tester a = Tester {runTester :: TesterConfig -> IO a}

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
--   find the RTS library (libtrioletrts.so)
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

-- | Read a test case, given test case directory.
--   The information is read from a file called \"config\" in the directory.
--   If the file cannot be read, an exception is thrown.
loadTestSpec :: TesterConfig -> FilePath -> IO SourceTest
loadTestSpec tester_config path = do
  config_text <- readFile (path </> "config")
  config <-
    case reads config_text
    of (test_case, rest):_ 
         | all isSpace rest -> return test_case
       _ -> fail $ "Malformed configuration file: " ++ (path </> "config")
  return $ mkSourceTest (TestSpec path config) tester_config

-- | Run a test and determine its result.
--
--   The test is run with the given path as its working directory.
--   The working directory is cleared after finishing the test case.
runSourceTest :: SourceTest -> FilePath -> IO (String, Statistics)
runSourceTest test@(SourceTest spec config) tmpdir = do
  result <- runTester (runTestHelper tmpdir spec) config
  return (show result, as_statistic result)
  where
    as_statistic TestSucceeded = passedStatistic test
    as_statistic (TestFailed _) = failedStatistic test

runTestHelper :: FilePath -> TestSpec -> Tester TestResult
runTestHelper temporary_path test_case = (return . TestFailed) `handleTester`
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
      mapM_ (compileTrioletFile temporary_path test_case) $
        testTrioletSources test_case
      mapM_ (compileLLTrioletFile temporary_path test_case) $
        testLLTrioletSources test_case
      mapM_ (compileCFile temporary_path test_case) $
        testCSources test_case
      mapM_ (compileCxxFile temporary_path test_case) $
        testCxxSources test_case
      linkTest temporary_path test_case

    run = do
      let prog = temporary_path </> testExecutableName
          
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

objectPath test_path file_path =
  test_path </> takeFileName file_path `replaceExtension` ".o"

-- | Attempt to do a step of compilation.  If the command fails, then return
-- an error message.
runCompileCommand fail_message program opts stdin = do
  (rc, _, err) <- liftIO $ dbReadProcessWithExitCode program opts stdin
  when (rc /= ExitSuccess) $
    liftIO $ throwIO $ CompileFailed (fail_message err)

-- | Compile a file using the 'triolet' compiler.  Used for both triolet and
--   lltriolet code.
compileUsingTrioletCompiler fail_message compile_flags = do
  build_dir <- asks buildDir
  let triolet_program_path = build_dir </> "triolet" </> "triolet"
      build_data_path = build_dir </> "data"
      flags = ["-B", build_data_path] -- Link to the local library files
              ++ compile_flags

  runCompileCommand fail_message triolet_program_path flags ""

compileTrioletFile test_path test_case file_path = do
  let obj_path = objectPath test_path file_path
      flags = ["-x", "triolet",    -- Compile in triolet mode
               file_path, "-o", obj_path]
      fail_message err = "File: " ++ file_path ++ "\n" ++ err

  compileUsingTrioletCompiler fail_message flags

compileLLTrioletFile test_path test_case file_path = do
  let obj_path = objectPath test_path file_path
      flags = ["-x", "lltriolet",    -- Compile in low-level triolet mode
               file_path, "-o", obj_path]
      fail_message err = "File: " ++ file_path ++ "\n" ++ err

  compileUsingTrioletCompiler fail_message flags

compileCFile test_path test_case file_path = do
  build_dir <- asks buildDir
  platform_opts <- asks platformCOpts
  let obj_path = objectPath test_path file_path
      opts = platform_opts ++
             ["-I", test_path,   -- Include files in the output directory
              "-I", build_dir </> "data" </> "include", -- Triolet library
              "-c", file_path,
              "-o", obj_path]
      fail_message err = "File: " ++ file_path ++ "\n" ++ err
  
  runCompileCommand fail_message "gcc" opts ""

compileCxxFile test_path test_case file_path = do
  build_dir <- asks buildDir
  platform_opts <- asks platformCOpts
  let obj_path = objectPath test_path file_path
      opts = platform_opts ++
             ["-I", test_path,   -- Include files in the output directory
              "-I", build_dir </> "data" </> "include", -- Triolet library
              "-c", file_path,
              "-o", obj_path]
      fail_message err = "File: " ++ file_path ++ "\n" ++ err
  
  runCompileCommand fail_message "g++" opts ""

linkTest test_path test_case = do
  build_dir <- asks buildDir
  platform_opts <- asks platformLinkOpts
  let c_file_paths = map (objectPath test_path) $ testCSources test_case
      cxx_file_paths = map (objectPath test_path) $ testCxxSources test_case
      lltriolet_file_paths = map (objectPath test_path) $
                             testLLTrioletSources test_case
      triolet_file_paths = map (objectPath test_path) $ testTrioletSources test_case
      link_opts = platform_opts ++ 
                  ["-o", testExecutableName] ++
                  cxx_file_paths ++ c_file_paths ++ lltriolet_file_paths ++ triolet_file_paths ++
                  ["-L" ++ build_dir </> "rts",
                   "-ltrioletrts", "-lgc", "-lm", "-lstdc++"]
      fail_message err = err

  runCompileCommand fail_message "gcc" link_opts ""
