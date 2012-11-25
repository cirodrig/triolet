{-| Custom configuration information.

The data type 'ExtraConfigFlags' holds configuration information that goes
beyond what Cabal supports.  This file also contains code for probing the
environment and saving configuration information.
-}

module SetupSrc.Config where

import Control.Exception
import Control.Monad
import Data.List hiding(isInfixOf)
import Distribution.Simple.Setup
import Distribution.Simple.Utils
import Distribution.Verbosity
import System.FilePath
import System.Directory
import System.IO

-- Path where we put extra configuration data
extraConfigPath = "dist" </> "extra-config"

-- | Parameters determined during configuration.  Cabal uses 'ConfigFlags';
--   the extra flags specific to this package are 'ExtraConfigFlags'.
data CustomConfigFlags =
  CustomConfigFlags
  { configExtraFlags :: !ExtraConfigFlags
  , configStdFlags :: !ConfigFlags
  }

setConfigStdFlags f c = c {configStdFlags = f}
setConfigExtraFlags f c = c {configExtraFlags = f}
modifyConfigExtraFlags c f = c {configExtraFlags = f (configExtraFlags c)}

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
    -- | Whether TBB is enabled
  , configTBB :: Bool
  }
  deriving (Read, Show)

defaultExtraConfigFlags :: ExtraConfigFlags
defaultExtraConfigFlags = ExtraConfigFlags [] [] [] [] True

-- Write custom configure information to a file
writeExtraConfigFile :: ExtraConfigFlags -> IO ()
writeExtraConfigFile config_data =
  rewriteFile extraConfigPath (show config_data)

-- Read custom configure information from a file
readExtraConfigFile :: IO ExtraConfigFlags
readExtraConfigFile =
  evaluate . read =<< readFile extraConfigPath

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

