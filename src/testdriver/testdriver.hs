-- The driver for the Pyon test suite.

{-# LANGUAGE ForeignFunctionInterface #-}
import TestCase

import Control.Monad
import Control.Monad.Trans
import Data.Monoid
import Foreign.Ptr
import Foreign.C.String
import System.FilePath
import System.Directory

foreign import ccall "unistd.h mkdtemp" c_mkdtemp :: CString -> IO CString

-- | Given a template file name, create a new directory
mkdtemp :: FilePath -> IO FilePath
mkdtemp path = withCString path $ \c_path -> do
  d_path <- c_mkdtemp c_path
  if d_path == nullPtr
    then fail "Cannot create temporary directory" 
    else peekCString d_path

getSubdirectories :: FilePath -> IO [FilePath]
getSubdirectories path = do
  contents <- getDirectoryContents path
  return [f | f <- contents, f /= ".", f /= ".."]

loadTests :: FilePath -> IO [TestCase]
loadTests base_path = do
  test_directories <- getSubdirectories base_path
  forM test_directories $ \subdir -> do
    loadTestCase (base_path </> subdir)

-- | Statistics about test results
data Statistics =
  Statistics
  { passed :: !Int
  , failed :: !Int
  }

passedStatistic, failedStatistic :: Statistics
passedStatistic = Statistics 1 0
failedStatistic = Statistics 0 1

testResultStatistic TestSucceeded = passedStatistic
testResultStatistic (TestFailed _) = failedStatistic

instance Monoid Statistics where
  mempty = Statistics 0 0
  mappend s1 s2 = Statistics (passed s1 + passed s2) (failed s1 + failed s2)
  mconcat ss = Statistics (sum $ map passed ss) (sum $ map failed ss)

runTests :: FilePath -> [TestCase] -> Tester ()
runTests tmpdir test_cases = do
  foldM run_test mempty test_cases
  return ()
  where
    run_test :: Statistics -> TestCase -> Tester Statistics
    run_test stats test_case = do
      liftIO $ putStrLn $ "Running " ++ testName test_case
      result <- runTest tmpdir test_case
      liftIO $ print result
      return $! stats `mappend` testResultStatistic result

main = do
  curdir <- getCurrentDirectory
  tests <- loadTests (curdir </> "test")

  tmp_base_dir <- getTemporaryDirectory
  tmpdir <- mkdtemp (tmp_base_dir </> "pyontest.XXXXXX")
  runTester $ runTests tmpdir tests
