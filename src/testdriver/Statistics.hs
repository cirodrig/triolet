
{-# LANGUAGE ExistentialQuantification, ForeignFunctionInterface, ScopedTypeVariables #-}
module Statistics where

import Control.Exception
import Control.Monad
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


-- A test that can be run
class Testable a where
  -- | Get the human-readable name of this test
  testName :: a -> String

  -- | Run this test.  The file path is the absolute path of a
  --   directory that the test should put all its temporary files in.
  --   A minimal, human-readable summary of the test results are returned, 
  --   along with information to be accumulated about the result of all tests.
  runTest :: a -> FilePath -> IO (String, Statistics)

data Test = forall a. Testable a => Test a

instance Testable Test where
  testName (Test x) = testName x
  runTest (Test x) tmpdir = runTest x tmpdir

-------------------------------------------------------------------------------

-- | Statistics about test results
data Statistics =
  Statistics
  { passed :: {-# UNPACK #-}!Int
  , failed :: [String]          -- ^ List of tests that failed
  }

instance Monoid Statistics where
  mempty = Statistics 0 []
  mappend s1 s2 = Statistics (passed s1 + passed s2) (failed s1 ++ failed s2)
  mconcat ss = Statistics (sum $ map passed ss) (concatMap failed ss)

passedStatistic, failedStatistic :: Testable a => a -> Statistics
passedStatistic _  = Statistics 1 []
failedStatistic tc = Statistics 0 [testName tc]

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

runTests :: forall a. Testable a => [a] -> IO ()
runTests tests = do
  -- Set up temporary directory for tests
  tmp_base_dir <- getTemporaryDirectory
  tmpdir <- mkdtemp (tmp_base_dir </> "pyontest.XXXXXX")
  bracket getCurrentDirectory setCurrentDirectory $ \_ -> do
    setCurrentDirectory tmpdir
    
    -- Run the tests
    statistics <- foldM (run_test tmpdir) mempty tests
    printStatistics statistics
  where
    -- Run a test and collect its results
    run_test :: forall. FilePath -> Statistics -> a -> IO Statistics
    run_test tmpdir stats test_case = do
      putStrLn $ "Running " ++ testName test_case
      (message, result) <- runTest test_case tmpdir
      putStrLn message
      return $! stats `mappend` result

-------------------------------------------------------------------------------

-- | Configuration information derived from the Cabal package configuration
data TesterConfig =
  TesterConfig
  { -- | Directory holding Pyon's build files
    buildDir :: !FilePath
    -- | Platform-specific options for the target C compiler
  , platformCOpts :: [String]
    -- | Platform-specific options for the target linker
  , platformLinkOpts :: [String]
    -- | Platform-specific options for the host C compiler
  , hostCOpts :: [String]
    -- | Platform-specific options for the host linker
  , hostLinkOpts :: [String]
  }

