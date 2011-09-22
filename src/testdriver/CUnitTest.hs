
module CUnitTest where

import Control.Exception
import Control.Monad
import Data.List
import Data.Monoid
import System.Exit
import System.FilePath
import System.Directory
import System.IO
import System.Posix.Env
import System.Process

import Statistics

data CUnitTest =
  CUnitTest
  { testDirectory :: FilePath
  , testConfig :: !TesterConfig
  }

instance Testable CUnitTest where
  testName test = takeFileName $ testDirectory test
  runTest test = runCUnitTest test

-- | Run a command with an altered environment variable
withEnv :: String -> (Maybe String -> String) -> IO a -> IO a
withEnv key alter_value m =
  bracket get_env reset_env $ \old_value -> do
    setEnv key (alter_value old_value) True
    m
  where
    get_env = getEnv key
    reset_env Nothing          = unsetEnv key
    reset_env (Just old_value) = setEnv key old_value True

-- | Run a command with an environment variable temporarily replaced
localEnv :: String -> String -> IO a -> IO a 
localEnv key value m = withEnv key (const value) m

localEnvList xs m = foldr (uncurry localEnv) m xs

-- | Read a test case, given test case directory.
loadCUnitTest :: TesterConfig -> FilePath -> IO CUnitTest
loadCUnitTest config path = return $ CUnitTest path config

runCUnitTest :: CUnitTest -> FilePath -> IO (String, Statistics)
runCUnitTest test temporary_path = do
  let run_process path args = do
        (_, _, _, hdl) <- createProcess $ proc path args
        waitForProcess hdl

  -- Run makefile
  let makefile_path = testDirectory test </> "Makefile"
  rc <- setupBuildEnv test temporary_path $
        run_process "make" ["-f", makefile_path]
  if rc /= ExitSuccess then return make_failed else do
    
    -- Run program
    rc <- run_process (temporary_path </> "unittest") []
    if rc /= ExitSuccess then return run_failed else return run_succeeded
  where
    make_failed = ("Could not build unit test", failedStatistic test)
    run_failed = ("Run failed", failedStatistic test)
    run_succeeded = ("Passed", passedStatistic test)
    
setupBuildEnv :: CUnitTest -> FilePath -> IO a -> IO a
setupBuildEnv test temporary_path m = localEnvList environment m
  where
    config = testConfig test
    environment = [ ("TARGET", temporary_path </> "unittest")
                  , ("SRCDIR", testDirectory test)
                  , ("BUILDDIR", buildDir config)
                  , ("CCFLAGS", intercalate " " $ hostCOpts config)
                  , ("LINKFLAGS", intercalate " " $ hostLinkOpts config)]
