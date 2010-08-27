{-| Regression testing.
-}

{-# LANGUAGE DeriveDataTypeable #-}
module SetupTest where

import Prelude hiding(catch)

import Control.Monad
import Control.Exception
import Data.List
import Data.Typeable
import System.Cmd
import System.Directory
import System.Exit
import System.FilePath
import System.Posix.Directory
import System.Process

import SetupPaths

-- | The expected result of a regression test.
data ExpectedTestResult =
    ShouldNotCompile            -- ^ Compiler should reject with an error
  | ShouldCompile               -- ^ Compiler should create an executable
  | ShouldRun                   -- ^ Test should run and print correct output
    deriving(Read, Show)

data TestResult = Pass | Fail

-- | A regression test.
--
-- Source files are compiled in the order they are given.
data RegressionTest =
  RegressionTest
  { testDir :: !String          -- ^ Test directory name
  , testResult :: !ExpectedTestResult
  , testPyonSources :: ![FilePath]
  , testPyasmSources :: ![FilePath]
  , testCSources :: ![FilePath]
  }
  deriving(Read, Show)

-- | Exceptions during regression testing
data RegressionExc =
    CompileFailed FilePath
  | CompileDidn'tFail           -- ^ Should have failed
  | LinkFailed
  | TestFailed Int
  | OutputMismatched String
  | OtherProgramFailed String
  deriving(Typeable)

instance Show RegressionExc where
  show (CompileFailed path) = "Compiler failed when compiling " ++ path
  show CompileDidn'tFail = "Compiler accepted bad input"
  show LinkFailed = "Linking failed"
  show (TestFailed ec) = "Test failed with error code " ++ show ec
  show (OutputMismatched str) = "Test output does not match expected output"
  show (OtherProgramFailed str) = "Program failed: " ++ str

instance Exception RegressionExc

-- | Run a system command to compile a file.  Throw an exception if it fails.
rawSystemCompile :: String -> [String] -> FilePath -> IO ()
rawSystemCompile cmd args file_path = do
  putStrLn $ intercalate " " (cmd : args)
  code <- rawSystem cmd args
  case code of
    ExitFailure _ -> throwIO $ CompileFailed file_path
    ExitSuccess -> return ()

-- | Run a system command.  Throw an exception if it fails.
rawSystemUtil :: String -> [String] -> IO ()
rawSystemUtil cmd args = do
  putStrLn $ intercalate " " (cmd : args)
  code <- rawSystem cmd args
  case code of
    ExitFailure _ ->
      throwIO $ OtherProgramFailed $ intercalate " " (cmd : args)
    ExitSuccess -> return ()

compilePyonFile path =
  rawSystemCompile "pyon" ["-x", "pyon", path] path

compilePyasmFile path =
  rawSystemCompile "pyon" ["-x", "pyasm", path] path

compileCFile path =
  rawSystemCompile "gcc" ["-c", path] path

linkObjectFiles = do
  contents <- getDirectoryContents "."
  let objects = filter ((".o" ==) . takeExtension) contents
  ec <- rawSystem "gcc" objects
  case ec of
    ExitFailure _ -> throwIO LinkFailed
    ExitSuccess -> return ()

-------------------------------------------------------------------------------

-- | Compile a regression test.
--
-- The current directory should be the build/test directory.
compileRegressionTest :: FilePath -> RegressionTest -> IO ()
compileRegressionTest test_root test = do
  mapM_ compilePyonFile $ map full_source_path $ testPyonSources test
  mapM_ compilePyasmFile $ map full_source_path $ testPyasmSources test
  mapM_ compileCFile $ map full_source_path $ testCSources test
  linkObjectFiles
  where  
    full_source_path f = test_root </> testDir test </> f

-- | Execute a regression test program.
--
-- The test must be compiled first.  Its output will be redirected to stdout,
-- and its error code will be checked.
executeRegressionTest :: FilePath -> RegressionTest -> IO ()
executeRegressionTest test_root test = do
  cwd <- getWorkingDirectory
  let exename = cwd </> "a.out"
  (_, _, _, proc_hdl) <- createProcess $ (proc exename []) {std_err = Inherit}
  ec <- waitForProcess proc_hdl
  case ec of
    ExitFailure n -> throwIO (TestFailed n)
    ExitSuccess -> return ()
  
runRegressionTest :: FilePath -> RegressionTest -> IO TestResult
runRegressionTest test_root test = do
  print_start
  inCleanTestDir (do_test (testResult test) >> print_test_success) `catch`
    print_test_failure
  where
    do_test ShouldNotCompile = do
      compileRegressionTest test_root test `catch` check_not_compile
      throwIO CompileDidn'tFail
    
    do_test ShouldCompile = do
      compileRegressionTest test_root test

    do_test ShouldRun = do
      compileRegressionTest test_root test
      executeRegressionTest test_root test

    check_not_compile exc =
      case exc
      of CompileFailed {} -> return ()
         _ -> throwIO exc

    print_start = putStrLn $ "STARTING " ++ testDir test
    print_test_success = do putStrLn $ "PASSED   " ++ testDir test
                            return Pass

    print_test_failure :: RegressionExc -> IO TestResult
    print_test_failure _ = do putStrLn $ "FAILED   " ++ testDir test
                              return Fail

-- | Run the computation in a clean working directory.  The directory name is  
-- fixed, and it must not already exist.  The working directory and its
-- contents will be deleted at the end.
inCleanTestDir :: IO a -> IO a
inCleanTestDir m = do
  cwd <- getWorkingDirectory
  bracket make_tmp_dir (remove_tmp_dir cwd) (const m)
  where
    make_tmp_dir = do
      System.Directory.createDirectory "regrtest"
      changeWorkingDirectory "regrtest"

    remove_tmp_dir cwd _ = do
      changeWorkingDirectory cwd
      rawSystem "rm" ["-r", "regrtest"]

-- | Find regression tests.  List the subdirectories of the test directory,
-- find the test description in each.
findRegressionTests :: FilePath -> IO [RegressionTest]
findRegressionTests dir = do
  contents <- getDirectoryContents dir
  mapM read_regression_test [x | x <- contents, x /= ".", x /= ".."]
  where
    read_regression_test subdir = report_exception `handle` do
      descr <- readFile $ dir </> subdir </> "info"
      test_info <- evaluate (read descr)
      when (testDir test_info /= subdir) $
        fail "Test directory does not match actual directory name"
      return test_info
      where
        report_exception e = do
          putStrLn $ "Malformed or missing \"info\" file in directory " ++ show subdir ++ ":"
          print (e :: IOException)
          throwIO e

data TestStatistics =
  TestStatistics
  { numPassed :: !Int
  , numFailed :: !Int
  }

emptyStatistics = TestStatistics 0 0

updateStatistics stats Pass = stats {numPassed = numPassed stats + 1}
updateStatistics stats Fail = stats {numFailed = numFailed stats + 1}

printStatistics stats = do
  putStrLn "Summary statistics"
  putStrLn $ "Passed: " ++ show (numPassed stats)      
  putStrLn $ "Failed: " ++ show (numFailed stats)

runRegressionTests = catchError `handle` do
  cwd <- getWorkingDirectory
  let test_dir = cwd </> testSourceDir
  
  tests <- findRegressionTests test_dir
  run_tests test_dir emptyStatistics tests
  return ()
  where
    catchError exc = do
      print (exc :: RegressionExc)
      return ()

    run_tests dir stats (test:tests) = do
      result <- runRegressionTest dir test
      stats' <- evaluate $ updateStatistics stats result
      run_tests dir stats' tests
    
    run_tests _ stats [] = printStatistics stats
