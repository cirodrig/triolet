{-| Specifications of work to be performed by an invocation of the compiler.
-}

{-# LANGUAGE GADTs, Rank2Types #-}
module Job
       (-- * Intermediate files
        File,
        -- ** Creating files
        diskFile,
        newTemporaryFile,
        -- ** Reading and writing files
        getFilePath,        
        readDataFile,
        readDataFileString,
        writeDataFile,
        writeDataFileString,
        
        -- * Jobs
        Task(..),
        Job,
        taskJob,
        pass,
        runJob
        )
where

import Control.Monad
import Data.ByteString(ByteString)
import qualified Data.ByteString as ByteString
import Data.IORef
import System.Directory
import System.Random

import Gluon.Common.Error
import qualified LowLevel.Syntax as LowLevel

-- | Make a temporary file name.  Race conditions are possible.
tmpnam :: String -> IO FilePath
tmpnam suffix = do
  random_chars <- replicateM 4 $ fmap (tmpnamTable !!) $ randomRIO (0, 61)
  let fname = "/tmp/pyon" ++ random_chars ++ suffix
  exists <- doesFileExist fname
  if exists then tmpnam suffix else return fname

tmpnamTable = ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9']

-- | A reference to a file that is read or written by a 'Job'.
-- Files are not open unless they're being read or written.
data File =
    -- | A file on disk
    DiskFile FilePath
    -- | A temporary anonymous file on disk.  A name is created when
    -- the file is written.  The given suffix, which usually should start with 
    -- a dot, is combined with random text to create the file name.
  | TemporaryFile String !(IORef (Maybe FilePath))

diskFile :: FilePath -> File
diskFile = DiskFile

newTemporaryFile :: String -> IO File
newTemporaryFile suffix = do
  pathref <- newIORef Nothing
  return $ TemporaryFile suffix pathref

readDataFileAs :: (FilePath -> IO a) -> File -> IO a
readDataFileAs reader file = 
  case file
  of DiskFile path -> reader path
     TemporaryFile _ pathref -> do
       path <- readIORef pathref
       case path of
         Just p  -> reader p
         Nothing ->
           internalError "Attempted to read temporary file before creating it"

readDataFile :: File -> IO ByteString
readDataFile = readDataFileAs ByteString.readFile

readDataFileString :: File -> IO String
readDataFileString = readDataFileAs readFile

writeDataFileAs :: (FilePath -> a -> IO ()) -> File -> a -> IO ()
writeDataFileAs writer file contents = 
  case file
  of DiskFile path -> writer path contents
     TemporaryFile suffix pathref -> do
       path <- getFilePath file
       writer path contents

writeDataFile :: File -> ByteString -> IO ()
writeDataFile = writeDataFileAs ByteString.writeFile

writeDataFileString :: File -> String -> IO ()
writeDataFileString = writeDataFileAs writeFile
  
-- | Get the path to an intermediate file.  If it's a random temporary file,
-- a randomized path will be created.
getFilePath :: File -> IO FilePath
getFilePath (DiskFile path) = return path
getFilePath (TemporaryFile suffix pathref) = do
  path <- readIORef pathref
  case path of
    Just p -> return p
    Nothing -> do p <- tmpnam suffix
                  writeIORef pathref (Just p)
                  return p

-- | A single step within a job.  The implementation of each task is provided 
-- elsewhere.
data Task a where
  -- | Fetch data from a file
  ReadInputFile          :: FilePath -> Task File
  -- | Run CPP on a file
  PreprocessCPP          :: File -> Task File
  -- | Parse a PyonAsm file
  ParsePyonAsm           :: File -> Task LowLevel.Module
  -- | Compile a Pyon file
  CompilePyonToPyonAsm   :: File -> Task LowLevel.Module
  -- | Compile a PyonAsm file
  CompilePyonAsmToObject :: LowLevel.Module -> Task File
  -- | Move output to a specific path.  If possible, move the input file.
  -- The input file should no longer be available after the move.
  RenameToPath           :: FilePath -> File -> Task ()

-- | Work for the compiler to do.
data Job a where
  Task   :: Task a -> Job a
  Bind   :: Job a -> (a -> Job b) -> Job b
  Return :: a -> Job a

-- | Create a job consisting of one task.
taskJob :: Task a -> Job a
taskJob = Task

pass :: Job ()
pass = return ()

instance Monad Job where
  return = Return
  (>>=) = Bind

-- | Run a job, given a task interpreter.
runJob :: (forall a. Task a -> IO a) -> Job a -> IO a
runJob runTask job = run job
  where
    run :: forall a. Job a -> IO a
    run (Task t) = runTask t
    run (Bind t k) = do run . k =<< run t
    run (Return x) = return x
