{-| Regression test cases.
-}

{-# LANGUAGE DeriveDataTypeable #-}
module TestCase where

import Prelude hiding(catch)

import Control.Monad
import Control.Monad.Trans
import Control.Exception
import Data.Char
import Data.List
import Data.Typeable
import System.Exit
import System.Directory
import System.FilePath
import System.IO
import System.Process

-- | Print a command before running it
dbReadProcessWithExitCode prog args stdin = do
  when debug $ liftIO $ print $ intercalate " " (prog : args)
  readProcessWithExitCode prog args stdin
  where
    debug = False

newtype Tester a = Tester {runTester :: IO a}

instance Monad Tester where
  return x = Tester (return x)
  m >>= k = Tester $ do x <- runTester m
                        runTester (k x)

instance MonadIO Tester where
  liftIO m = Tester m

handleTester :: Exception e => (e -> Tester a) -> Tester a -> Tester a
handleTester = flip catchTester

catchTester :: Exception e => Tester a -> (e -> Tester a) -> Tester a
catchTester m handler = 
  Tester $ (\e -> runTester (handler e)) `handle` runTester m 

-- | Run a command in a different directory
withDirectory :: FilePath -> Tester a -> Tester a
withDirectory path (Tester tester) = Tester $
  bracket getCurrentDirectory setCurrentDirectory $ \_ -> do 
    setCurrentDirectory path
    tester

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
  , cSources :: ![FilePath]
  , expectedResult :: !ExpectedResult
  }
  deriving(Read, Show)

testSynopsis = synopsis . testConfig

testName = takeFileName . testDirectory

testPyonSources tc = 
  [testDirectory tc </> file | file <- pyonSources $ testConfig tc]
  
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
                   then "No output on stdout\n"
                   else "First few characters of stdout:\n" ++ take 160 out
        err_text = if null err 
                   then "No output on stderr\n"
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
runTest :: FilePath             -- ^ Directory for temporary files
        -> TestCase             -- ^ Test case to run
        -> Tester TestResult
runTest test_path test_case = withDirectory test_path run_test_case
  where
    -- Run a test case.  Return the test result.
    run_test_case :: Tester TestResult
    run_test_case = (return . TestFailed) `handleTester`
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

    compile_and_link = do
      mapM_ (compilePyonFile test_path test_case) $ testPyonSources test_case
      mapM_ (compileCFile test_path test_case) $ testCSources test_case
      linkTest test_path test_case

    run = liftIO $ do
      (rc, out, err) <- readProcessWithExitCode testExecutableName [] ""
      case rc of 
        ExitSuccess   -> return (out, err)
        ExitFailure _ -> throwIO $
                         RunFailed { resultCode = rc 
                                   , resultStdoutLog = out
                                   , resultStderrLog = err}

    check_output expected_out out =
      if expected_out /= out
      then liftIO $ throwIO $ CheckFailed expected_out out
      else return ()

compilePyonFile test_path test_case file_path = liftIO $ do
  (rc, _, err) <- dbReadProcessWithExitCode "pyon" flags ""
  when (rc /= ExitSuccess) $
    throwIO $ CompileFailed (fail_message err)
  where
    flags = ["-x", "pyon", file_path, "-o", obj_path]
    obj_path = test_path </> takeFileName file_path `replaceExtension` ".o"
    fail_message err = "File: " ++ file_path ++ "\n" ++ err

compileCFile test_path test_case file_path = liftIO $ do
  (rc, _, err) <- dbReadProcessWithExitCode "gcc" flags ""
  when (rc /= ExitSuccess) $
    throwIO $ CompileFailed (fail_message err)
  where
    flags = ["-c", file_path, "-o", obj_path]
    obj_path = test_path </> takeFileName file_path `replaceExtension` ".o"
    fail_message err = "File: " ++ file_path ++ "\n" ++ err

linkTest test_path test_case = liftIO $ do
  (rc, _, err) <- dbReadProcessWithExitCode "gcc" link_arguments ""
  when (rc /= ExitSuccess) $
    throwIO $ CompileFailed (fail_message err)
  where
    fail_message err = err
    
    link_arguments = ["-o", testExecutableName] ++
                     c_file_paths ++ pyon_file_paths
  
    c_file_paths = [test_path </> takeFileName file `replaceExtension` ".o"
                   | file <- testCSources test_case]
    pyon_file_paths = [test_path </> takeFileName file `replaceExtension` ".o"
                      | file <- testPyonSources test_case]

