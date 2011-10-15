{-| Specifications of work to be performed by an invocation of the compiler.

The command line interpreter constructs a 'Job' that indicates everything
the compiler will do.  The job is then interpreted with 'runJob'.

Some tasks in a Job get their input or write their output to files.  We can't
abstract files as Handles, because we don't want to keep them open all the
time, nor as FilePaths, because some files exist at randomly generated paths
created on the fly.  Files
are represented by the types 'ReadFile' (for input), 'WriteFile' (for output), 
and 'TempFile' (for output followed by input).  File contents may be
accessed directly, or their
path may be retrieved for ordinary file I/O.
-}

{-# LANGUAGE GADTs, Rank2Types, ForeignFunctionInterface #-}
module Job
       (-- * Intermediate files
        ReadFile, readFileFromPath, readTempFile,
        WriteFile, writeFileFromPath, writeTempFile, writeNothing,
        TempFile, tempFileFromPath,

        -- ** Reading and writing files
        readFileAsString,
        readFileAsByteString,
        readFilePath,
        writeFileAsString,
        writeFileAsByteString,
        writeFilePath,
        writeFileWithHandle,
        
        -- * Compilation flags
        CompileFlag(..),
        CompileFlags,
        lookupCompileFlag,

        -- * Jobs
        Task(..),
        Job,
        taskJob,
        pass,
        withAnonymousFile,
        runJob
        )
where

import Prelude hiding(catch)

import Control.Exception
import Control.Monad
import Data.ByteString.Lazy(ByteString)
import qualified Data.ByteString.Lazy as ByteString
import Data.IORef
import qualified Data.Set as Set
import Foreign.C
import Foreign.Ptr
import System.Directory
import System.FilePath
import System.IO
import System.Random

import Common.Error
import qualified SystemF.Syntax as SystemF
import qualified SystemF.MemoryIR as SystemF
import qualified LowLevel.Syntax as LowLevel
import qualified LowLevel.InterfaceFile as LowLevel

-- | Make a temporary file name.  Race conditions are possible.
tmpnam :: FilePath -> String -> IO FilePath
tmpnam dir suffix = do
  dir_exists <- doesDirectoryExist dir
  unless dir_exists $ fail $ "Directory does not exist: " ++ dir
  generate_tmpnam
  where
    -- Generate filenames until one is found
    generate_tmpnam = do
      random_chars <- replicateM 4 $ fmap (tmpnamTable !!) $ randomRIO (0, 63)
      let fname = dir </> "pyon" ++ random_chars ++ suffix
      exists <- doesFileExist fname
      if exists then generate_tmpnam else return fname

tmpnamTable = '_' : '-' : ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9']

foreign import ccall "unistd.h mkdtemp" mkdtemp :: Ptr CChar -> IO (Ptr CChar)

-- | Create a temporary directory.  The directory name is returned.
tmpdir :: IO FilePath
tmpdir = withCString "/tmp/pyon.XXXXXX" $ \template -> do
  dirname <- mkdtemp template
  if dirname == nullPtr
    then throwErrno "Creating directory for temporary files"
    else peekCString dirname

-- | A file that is read by a 'Job'.
data ReadFile =
    -- | An input file on disk
    DiskReadFile !FilePath
    -- | A temporary input ifle
  | TempReadFile !TempFile

-- | A file that is written by a 'Job'.
data WriteFile =
    -- | A file on disk.  If the file exists, it will be overwritten.
    DiskWriteFile !FilePath
    -- | A temporary output file
  | TempWriteFile !TempFile
    -- | Discard output
  | NullWriteFile

-- | An intermediate file that is the output of one 'Job' and the input of
-- others.  The intermediate file may either be deleted, or persist after
-- all jobs complete. 
--
-- Temporary files must be written before being read.
data TempFile =
    -- | An anonymous temporary file on disk.  A name is created when the file
    --   is opened.
    DiskTempFile {-#UNPACK#-} !(IORef DiskTempFile)

-- | The state of a temporary file on disk.  The file state is held in an
-- 'IORef' and is updated as the situation changes.
data DiskTempFile =
    -- | An anonymous temporary file that has not been created yet.
    -- The given directory path and suffix will be combined with a random
    -- filename.
    PendingAnonDF 
    { tempFileParentDirectory :: !FilePath 
    , tempFileSuffix :: !String
    }

    -- | A named temporary file that has not been created yet.  If the flag
    -- is true, the existing file will be overwritten (if present).
  | PendingNamedDF 
    { tempFileMayOverwrite :: !Bool 
    , tempFilePath :: !FilePath
    }

    -- | A temporary file that has been written.
  | WrittenDF 
    { tempFileShouldBeDeleted :: !Bool 
    , tempFilePath :: !FilePath
    }

-- | Reference an input file that exists in the filesystem
readFileFromPath :: FilePath -> ReadFile
readFileFromPath path = DiskReadFile path

-- | Reference an intermediate file for reading
readTempFile :: TempFile -> ReadFile 
readTempFile tf = TempReadFile tf

-- | Reference an output file.  If the file exists, it will be overwritten.
writeFileFromPath :: FilePath -> WriteFile
writeFileFromPath path = DiskWriteFile path

-- | Reference an intermediate file for writing
writeTempFile :: TempFile -> WriteFile
writeTempFile tf = TempWriteFile tf

-- | Discard output
writeNothing :: WriteFile
writeNothing = NullWriteFile

-- | Reference a named intermediate file
tempFileFromPath :: Bool        -- ^ Overwrite?
                 -> FilePath    -- ^ File path
                 -> IO TempFile
tempFileFromPath overwrite path =
  liftM DiskTempFile $ newIORef $ PendingNamedDF overwrite path

-- | Read a file's contents using the given reader function
readFileHelper :: (FilePath -> IO a) -> ReadFile -> IO a
readFileHelper read_file in_file =
  case in_file
  of DiskReadFile path -> read_file path
     TempReadFile (DiskTempFile flref) -> readIORef flref >>= input_temp_file
  where
    input_temp_file (PendingAnonDF {}) = read_before_write
    input_temp_file (PendingNamedDF {}) = read_before_write
    input_temp_file (WrittenDF {tempFilePath = path}) = read_file path
  
    read_before_write =
      fail "Attempted to read temporary file before writing"

-- | Read a file's contents as a string
readFileAsString :: ReadFile -> IO String
readFileAsString = readFileHelper readFile

-- | Read a file's contents as a string
readFileAsByteString :: ReadFile -> IO ByteString
readFileAsByteString = readFileHelper ByteString.readFile

-- | Get the input file path.  The file's contents will be read.
readFilePath :: ReadFile -> IO FilePath
readFilePath = readFileHelper return

writeFileHelper :: (FilePath -> a -> IO b) -> WriteFile -> a -> IO b
writeFileHelper write_file out_file contents =
  case out_file
  of DiskWriteFile path -> write_file path contents
     TempWriteFile (DiskTempFile flref) ->
       readIORef flref >>= output_temp_file flref
     NullWriteFile -> write_file "/dev/null" contents
  where
    output_temp_file flref (PendingAnonDF { tempFileParentDirectory = dir
                                          , tempFileSuffix = suffix}) = do
      -- Create a temporary file name.  The file does not exist.
      fname <- tmpnam dir suffix
      
      -- Write the file
      ret <- write_file fname contents
      
      -- Update the temporary file status
      writeIORef flref $
        WrittenDF { tempFileShouldBeDeleted = True
                  , tempFilePath = fname
                  }

      return ret

    output_temp_file flref (PendingNamedDF { tempFileMayOverwrite = overwrite
                                           , tempFilePath = path}) = do
      -- Check if the given path is a valid file path.  Write permissions are 
      -- not checked here; rather, we check for exceptions when trying to write
      path_exists <- doesDirectoryExist $ takeDirectory path
      unless path_exists $ cannot_write path "parent directory does not exist"

      dir_exists <- doesDirectoryExist path
      when dir_exists $ cannot_write path "file is a directory"

      -- If file exists and overwriting is disallowed, throw an exception
      when (not overwrite) $ do
        exists <- doesFileExist path
        when exists $ cannot_write path "file exists"

      -- Write the file
      ret <- write_file path contents
      
      -- Update the temporary file status
      writeIORef flref $
        WrittenDF { tempFileShouldBeDeleted = False
                  , tempFilePath = path
                  }

      return ret
    
    output_temp_file _ (WrittenDF {}) = already_written

    cannot_write path reason =
      fail $ "Cannot write output file '" ++ path ++ "': " ++ reason
    
    already_written =
      internalError "Attempted to overwrite an intermediate file"

-- | Write the file's contents
writeFileAsString :: WriteFile -> String -> IO ()
writeFileAsString NullWriteFile _ = return ()
writeFileAsString fl str = writeFileHelper writeFile fl str

-- | Write the file's contents
writeFileAsByteString :: WriteFile -> ByteString -> IO ()
writeFileAsByteString NullWriteFile _ = return () 
writeFileAsByteString fl str = writeFileHelper ByteString.writeFile fl str

-- | Write the file's contents
writeFilePath :: WriteFile -> IO FilePath
writeFilePath file = writeFileHelper (\path () -> return path) file ()

-- | Write the file's contents to a handle.  The handle will be closed once
--   writing is complete.
writeFileWithHandle :: WriteFile -> (Handle -> IO ()) -> IO ()
writeFileWithHandle NullWriteFile _ = return ()
writeFileWithHandle fl writer = writeFileHelper open_and_write fl writer
  where
    open_and_write path writer = do
      hdl <- openFile path WriteMode
      writer hdl
      hClose hdl

-------------------------------------------------------------------------------
-- User-configurable flags

-- | A user-configurable boolean flag affecting compilation
data CompileFlag =
    DoParallelization        -- ^ Enable parallelizing transformations
    deriving (Eq, Ord, Enum)

type CompileFlags = Set.Set CompileFlag

lookupCompileFlag :: CompileFlag -> CompileFlags -> Bool
lookupCompileFlag flg set = Set.member flg set

-------------------------------------------------------------------------------
-- Tasks

-- | A single step within a job.  The implementation of each task is provided 
-- elsewhere.
data Task a where
  -- Run CPP on a file
  PreprocessCPP          
    { cppMacros :: [(String, Maybe String)]
    , cppIncludeSearchPaths :: [FilePath]
    , cppInput :: ReadFile
    , cppOutput :: WriteFile
    } :: Task ()

  -- Parse a PyonAsm file
  ParsePyonAsm
    { parseAsmInput :: ReadFile
    } :: Task LowLevel.Module

  -- Parse a Pyon file and compile it to a high-level, unoptimized module
  ParsePyon
    { parseFlags :: CompileFlags
    , parsePyonInput :: ReadFile
    } :: Task (SystemF.Module SystemF.Mem)

  GetBuiltins :: Task (SystemF.Module SystemF.Mem)

  -- Compile a high-level, unoptimized module to a low-level module
  CompilePyonMemToPyonAsm
    { compileFlags :: CompileFlags
    , compileMemInput :: SystemF.Module SystemF.Mem
    } :: Task LowLevel.Module

  -- Compile a PyonAsm file
  CompilePyonAsmToGenC
    { compileAsmInput :: LowLevel.Module
    , compileAsmIfaces :: [LowLevel.Interface] -- ^ Interfaces to link with
    , compileAsmOutput :: WriteFile -- ^ Output C file
    , compileAsmInterface :: WriteFile -- ^ Output Pyon interface file
    , compileAsmHeader :: WriteFile -- ^ Header for exported C functions
    , compileAsmCxxHeader :: WriteFile -- ^ Header for exported C++ functions
    } :: Task ()
  -- Load an interface file
  LoadIface
    { loadIfaceInput :: ReadFile
    } :: Task LowLevel.Interface
  -- Compile a generated C file to object code
  CompileGenCToObject
    { compileGenCInput :: ReadFile
    , compileGenCOutput :: WriteFile
    } :: Task ()

-- | Work for the compiler to do.
data Job a where
  Task      :: Task a -> Job a
  Bind      :: Job a -> (a -> Job b) -> Job b
  Return    :: a -> Job a
  Bracket   :: IO a -> (a -> IO b) -> (a -> Job c) -> Job c
  GetTmpDir :: Job FilePath

-- | Create a job consisting of one task.
taskJob :: Task a -> Job a
taskJob = Task

-- | Run a job that uses a temporary file.  The file will be created in
-- a temporary directory, and deleted after compilation is done.
withAnonymousFile :: String -> (TempFile -> Job b) -> Job b
withAnonymousFile suffix job = do
  tmp_dir <- GetTmpDir
  Bracket (new_anon tmp_dir) delete_anon job
  where
    new_anon dir = liftM DiskTempFile $ newIORef $ PendingAnonDF dir suffix
    delete_anon (DiskTempFile tf) = readIORef tf >>= del
      where
        del (PendingAnonDF {}) = return () -- File was not created

        del (PendingNamedDF {}) =
          internalError "Anonymous file became named"

        del (WrittenDF { tempFileShouldBeDeleted = should_delete
                       , tempFilePath = path})
          | should_delete = removeFile path
          | otherwise = internalError "Anonymous file not marked for deletion"

pass :: Job ()
pass = return ()

instance Monad Job where
  return = Return
  (>>=) = Bind

-- | Run a job, given a task interpreter.
--
-- A temporary data directory will be created
runJob :: (forall a. Task a -> IO a) -> Job a -> IO a
runJob run_task job = do
  -- Create a directory for temporary files
  tmp_dir <- tmpdir
  
  -- Run the job
  x <- interpretJob run_task tmp_dir job
  
  -- Delete the directory (should be empty)
  removeDirectory tmp_dir `catch` \e -> do
    print ("Couldn't remove directory with temporary files: " ++
           show (e :: IOException))

  return x

interpretJob :: (forall a. Task a -> IO a) -> FilePath -> Job a -> IO a
interpretJob interpret_task tmp_dir job = run job
  where
    run :: forall a. Job a -> IO a
    run (Task t) = interpret_task t
    run (Bind t k) = do run . k =<< run t
    run (Return x) = return x
    run (Bracket begin end m) = bracket begin end $ \x -> run (m x)
    run GetTmpDir = return tmp_dir