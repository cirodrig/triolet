-- The driver for the Pyon test suite.

import Control.Monad
import Control.Monad.Trans
import Data.List
import Data.Monoid
import System.Environment
import System.FilePath
import System.Directory

import Statistics
import TestCase
import CUnitTest

sourceTestPath :: FilePath -> FilePath
sourceTestPath base_path = base_path </> "test" </> "source"

unitTestPath :: FilePath -> FilePath
unitTestPath base_path = base_path </> "test" </> "unit"

getSubdirectories :: FilePath -> IO [FilePath]
getSubdirectories path = do
  contents <- getDirectoryContents path
  return [f | f <- contents, f /= ".", f /= ".."]

loadSourceTests :: TesterConfig -> FilePath -> IO [Test]
loadSourceTests config base_path = do
  test_directories <- getSubdirectories base_path
  let sorted_tests = sort test_directories
  forM sorted_tests $ \subdir -> do
    liftM Test $ loadTestSpec config (base_path </> subdir)

-- | Find a source test by name.  If the name matches, load it.
loadSourceTest :: TesterConfig -> FilePath -> String -> IO (Maybe Test)
loadSourceTest config test_parent_dir test_name = do
  let test_dir = test_parent_dir </> test_name
  exists <- doesDirectoryExist test_dir
  if exists
    then liftM (Just . Test) $ loadTestSpec config test_dir
    else return Nothing
  
loadUnitTests :: TesterConfig -> FilePath -> IO [Test]
loadUnitTests config base_path = do
  test_directories <- getSubdirectories base_path
  let sorted_tests = sort test_directories
  forM sorted_tests $ \subdir -> do
    liftM Test $ loadCUnitTest config (base_path </> subdir)

-- | Find a unit test by name.  If the name matches, load it.
loadUnitTest :: TesterConfig -> FilePath -> String -> IO (Maybe Test)
loadUnitTest config test_parent_dir test_name = do
  let test_dir = test_parent_dir </> test_name
  exists <- doesDirectoryExist test_dir
  if exists
    then liftM (Just . Test) $ loadCUnitTest config test_dir
    else return Nothing

loadAllTests config package_dir = do
  source_tests <- loadSourceTests config (sourceTestPath package_dir)
  unit_tests <- loadUnitTests config (unitTestPath package_dir)
  return $ unit_tests ++ source_tests

loadNamedTests config package_dir names = mapM load_test names
  where
    try_maybe m fallback = do
      x <- m
      case x of
        Nothing -> fallback
        Just y -> return y

    load_test test_name =
      try_maybe (loadSourceTest config (sourceTestPath package_dir) test_name) $
      try_maybe (loadUnitTest config (unitTestPath package_dir) test_name) $
      fail $ "Test case does not exist: " ++ test_name

main = do
  -- Set up paths
  rel_build_dir : extra_cflags : extra_lflags : host_cflags : host_lflags : other_args <- getArgs 
  build_dir <- canonicalizePath rel_build_dir 
  curdir <- getCurrentDirectory

  let tester_config =
        TesterConfig { buildDir = build_dir
                     , platformCOpts = read extra_cflags
                     , platformLinkOpts = read extra_lflags
                     , hostCOpts = read host_cflags
                     , hostLinkOpts = read host_lflags}
  -- Parse arguments
  let test_loader =
        case other_args
        of [] -> loadAllTests tester_config curdir
           test_names -> loadNamedTests tester_config curdir test_names

  tests <- test_loader
  runTests tests


