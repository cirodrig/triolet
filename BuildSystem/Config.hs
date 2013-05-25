{-| Custom configuration information.

The data type 'ExtraConfigFlags' holds configuration information that goes
beyond what Cabal supports.  This file also contains code for probing the
environment and saving configuration information.
-}

module BuildSystem.Config where

import Control.Exception
import Control.Monad
import Data.List hiding(isInfixOf)
import Distribution.Simple.Setup
import Distribution.Simple.Utils
import Distribution.Verbosity
import System.FilePath
import System.Directory
import qualified System.Info
import System.IO

-- Path where we put extra configuration data
extraConfigPath = "dist" </> "extra-config"

data OperatingSystem = UnknownOS | Linux | Darwin
                     deriving(Read, Show)

data ExtraConfigFlags =
  ExtraConfigFlags
  { -- | Include directories to use when compiling target code
    configTargetIncludeDirs :: [FilePath]
    -- | Library directories to use when compiling target code
  , configTargetLibDirs :: [FilePath]
    -- | Compiler-specific library directories to use when compiling
    --   target code.  These directories are found by querying the
    --   C++ compiler.
  , configCxxLibDirs :: [FilePath]
    -- | Extra flags to use when compiling C/C++ host code.
    --   On some systems, the \"-m32\" flag is required to be
    --   compatible with GHC output.
  , configHostArchFlags :: [String]
    -- | The operating system family on which target code runs
  , configTargetOS :: OperatingSystem
    -- | Whether TBB is enabled
  , configTBB :: Bool
    -- | Whether MPI is enabled
  , configMPI :: Bool
  }
  deriving (Read, Show)

defaultExtraConfigFlags :: ExtraConfigFlags
defaultExtraConfigFlags = ExtraConfigFlags [] [] [] [] UnknownOS False False

-- Write custom configure information to a file
writeExtraConfigFile :: ExtraConfigFlags -> IO ()
writeExtraConfigFile config_data =
  rewriteFile extraConfigPath (show config_data)

-- Read custom configure information from a file
readExtraConfigFile :: IO ExtraConfigFlags
readExtraConfigFile =
  evaluate . read =<< readFile extraConfigPath

-------------------------------------------------------------------------------

type ReadArg a = Either String a

-- | Read extra configuration flags from the command line.
--   Flags are given as a list of strings that must be parsed.
--   Returns an error message or the interpreted flags
readExtraConfigFlags :: [String] -> ReadArg ExtraConfigFlags
readExtraConfigFlags options =
  foldM readArgument defaultExtraConfigFlags (arguments options)

readArgument :: ExtraConfigFlags -> Argument -> ReadArg ExtraConfigFlags
readArgument flags (Argument key mval) =
  case lookup key dispatch_table
  of Nothing -> fail $ "Unrecognized configure option: " ++ show key
     Just m  -> m key mval flags
  where
    dispatch_table =
      [ ("target-include-dir", reqArg readTargetIncludeDir)
      , ("target-lib-dir", reqArg readTargetLibDir)
      , ("enable-tbb", noArg readEnableTBB)
      , ("enable-mpi", noArg readEnableMPI)
      ]

reqArg f _ (Just arg) flags = f arg flags
reqArg _ k (Nothing)  _ =
  fail $ "Configure option '" ++ k ++ "' requires an argument"

noArg f _ Nothing  flags = f flags
noArg f k (Just _) flags =
  fail $ "Configure option '" ++ k ++ "' doesn't take an argument"

readTargetIncludeDir arg flags =
  return $ flags {configTargetIncludeDirs = configTargetIncludeDirs flags ++ [arg]}

readTargetLibDir arg flags =
  return $ flags {configTargetLibDirs = configTargetLibDirs flags ++ [arg]}

readEnableTBB flags =
  return $ flags {configTBB = True}

readEnableMPI flags =
  return $ flags {configMPI = True}

-- | An argument is either a key or a key-value pair
data Argument = Argument String (Maybe String)

-- | Interpret arguments.  Arguments are of the form \"key=value\" or just
--   a key.
arguments :: [String] -> [Argument]
arguments ss = map split_arg ss
  where
    split_arg arg = split id arg
      where
        split hd ('=':val) = Argument (hd []) (Just val)
        split hd (c:cs)    = split (hd . (c:)) cs
        split hd []        = Argument (hd []) Nothing

-------------------------------------------------------------------------------

-- | Given the output string produced by @g++ -print-search-dirs@,
--   extract a list of library search paths.
--
--   Die with an error message if parsing fails.
extractGxxLibraryPaths :: Verbosity -> String -> IO [FilePath]
extractGxxLibraryPaths verb search_dirs =
  -- Find the "libraries:" line of the output
  case find ("libraries:" `isPrefixOf`) $ lines search_dirs
  of Just line ->
       case break ('=' ==) line
       of (_, '=':fields) -> filter_paths $ split fields
          _ -> failed
     _ -> failed
  where
    failed = die "Could not parse output of 'g++ -print-search-paths'"

    -- Split a colon-separated list of file names
    split fs =
      case break (':' ==) fs
      of ([]  , [])        -> []
         (path, ':' : fs') -> path : split fs'
         (path, [])        -> [path]

    -- Discard nonexistent file names
    filter_paths paths = filterM directory_exists paths
      where
        directory_exists path = do
          e <- doesDirectoryExist path
          when (not e) $
            info verb $ "Dropping non-existent C++ search path " ++ path
          return e

-- | Identify the target operating system
identifyTargetOS verb =
  -- Get the host OS, assume it's same as target OS
  case choose_os System.Info.os of
    Just os -> do
      info verb $ "Using " ++ System.Info.os ++ " as target operating system"
      return os
    Nothing ->
      die "Cannot identify target operating system"
  where
    choose_os "darwin" = Just Darwin
    choose_os "linux"  = Just Linux
    choose_os _        = Nothing

-- | Identify compiler flags needed to compile host C/C++ code
identifyHostCFlags verb = do
  -- Compile a minimal Haskell program
  tmpdir <- getTemporaryDirectory
  file_text <- withTempFile tmpdir "main.hs" $ \path hdl -> do 
    -- Create file
    hPutStr hdl "main = return ()\n" 
    hClose hdl

    -- Compile it
    let binary_file = tmpdir </> "cfgmain"
    rawSystemExit verb "ghc" [path, "-o", binary_file]

    -- Test the result
    file_text <- rawSystemStdout verb "file" ["-b", binary_file]
    removeFile binary_file
    return file_text

  return $ parseHostCFlagsOutput file_text

parseHostCFlagsOutput file_text
  | "x86_64" `isInfixOf` file_text ||
    "x86-64" `isInfixOf` file_text = []
  | "i386" `isInfixOf` file_text = ["-m32"]
  | otherwise = error "Unknown architecture"

-------------------------------------------------------------------------------

data TargetArchitectureParameters =
  TargetArchitectureParameters
  { -- | Pointer size on target architecture in bytes
    targetPointerSize :: !Int
    -- | Int size on target architecture in bytes
  , targetIntSize :: !Int
  }

computeTargetArchitectureParameters :: Verbosity
                                    -> IO TargetArchitectureParameters
computeTargetArchitectureParameters verb = do
  pointer_size <- getCSizeof verb "void *"
  int_size <- getCSizeof verb "int"
  return $ TargetArchitectureParameters { targetPointerSize = pointer_size
                                        , targetIntSize = int_size}

-- | Attempt to query the size of a data type by compiling and running a
--   C program.  The parameter string should be a valid C type.
--   The parameter string is not checked for validity.
getCSizeof :: Verbosity -> String -> IO Int
getCSizeof verb type_name = do
  tmpdir <- getTemporaryDirectory
  withTempDirectory verb tmpdir "setup." $ \mydir -> do
    let src_file = mydir </> "main.c"
        exe_file = mydir </> "main"

    info verb $ "Calculating sizeof(" ++ type_name ++ ")..."

    -- Create and run a C program to get the size
    writeFile src_file sizeof_code
    rawSystemExit verb "gcc" [src_file, "-o", exe_file]
    sizeof_string <- rawSystemStdout verb exe_file []
    size <- return $! read sizeof_string
    
    info verb $ "Calculated  sizeof(" ++ type_name ++ ") = " ++ show size
    return size
  where
    sizeof_code =
      "#include <stdio.h>\n" ++
      "int main() {\n" ++
      "  printf(\"%d\\n\", (int)sizeof(" ++ type_name ++ "));\n" ++
      "  return 0;\n" ++
      "}\n"

