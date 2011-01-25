-- The driver for the Pyon test suite.

{-# LANGUAGE ForeignFunctionInterface #-}
import TestCase

import Control.Monad
import Control.Monad.Trans
import Data.List
import Data.Monoid
import Foreign.Ptr
import Foreign.C.String
import System.Environment
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
  { passed :: {-# UNPACK #-}!Int
  , failed :: [String]          -- ^ List of tests that failed
  }

passedStatistic, failedStatistic :: TestCase -> Statistics
passedStatistic _  = Statistics 1 []
failedStatistic tc = Statistics 0 [testName tc]

testResultStatistic TestSucceeded = passedStatistic
testResultStatistic (TestFailed _) = failedStatistic

printStatistics :: Statistics -> IO ()
printStatistics s = do
  when (not $ null failed_list) $ do
    putStrLn "Failed tests:"
    putStrLn failed_list
  mapM_ putStrLn stat_text
  where
    stats = map mkstat [(passed s, "passed"), (length $ failed s, "failed")]
      where mkstat (n, label) = (n, show n, label)

    column_width = maximum [length s | (_, s, _) <- stats]
    align s = replicate (column_width - length s) ' ' ++ s
    stat_text = map mktext stats
      where
        mktext (n, num, label) =
          let plural_test = if n == 1 then "test" else "tests"
          in align num ++ " " ++ plural_test ++ " " ++ label

    failed_list = intercalate "\n" ["    " ++ s | s <- failed s]

instance Monoid Statistics where
  mempty = Statistics 0 []
  mappend s1 s2 = Statistics (passed s1 + passed s2) (failed s1 ++ failed s2)
  mconcat ss = Statistics (sum $ map passed ss) (concatMap failed ss)

runTests :: [TestCase] -> Tester ()
runTests test_cases = do
  statistics <- foldM run_test mempty test_cases
  liftIO $ printStatistics statistics
  where
    run_test :: Statistics -> TestCase -> Tester Statistics
    run_test stats test_case = do
      liftIO $ putStrLn $ "Running " ++ testName test_case
      result <- runTest test_case
      liftIO $ print result
      return $! stats `mappend` testResultStatistic result test_case

main = do
  -- Set up paths
  [rel_build_dir, extra_cflags, extra_lflags] <- getArgs 
  build_dir <- canonicalizePath rel_build_dir 
  curdir <- getCurrentDirectory

  -- Load tests
  tests <- loadTests (curdir </> "test")

  -- Run tests
  tmp_base_dir <- getTemporaryDirectory
  tmpdir <- mkdtemp (tmp_base_dir </> "pyontest.XXXXXX")
  
  let tester_config =
        TesterConfig { temporaryPath = tmpdir
                     , buildDir = build_dir
                     , platformCOpts = read extra_cflags
                     , platformLinkOpts = read extra_lflags}
  launchTester tester_config $ runTests tests
