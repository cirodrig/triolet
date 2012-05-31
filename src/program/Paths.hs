
module Paths where

import System.Environment
import System.FilePath
import qualified Paths_triolet

-- | Extract the data file path, if one was provided on the command line.
-- The data file path, if provided, must be first.
splitDataFilePath :: [String] -> (Maybe FilePath, [String])
splitDataFilePath ("-B" : path : args) = (Just path, args)
splitDataFilePath args = (Nothing, args)

-- | Get a data file name.  Use the path that was set when the program was 
-- configured, unless overridden on the command line.
getDataFileName :: FilePath -> IO FilePath
getDataFileName path = do
  args <- getArgs
  case fst $ splitDataFilePath args of
    Just data_path -> return (data_path </> path)
    Nothing        -> Paths_triolet.getDataFileName path
