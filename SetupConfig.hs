
module SetupConfig where

import Control.Exception
import Distribution.Simple.Setup
import Distribution.Simple.Utils
import Distribution.Verbosity
import System.FilePath
import System.Directory

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
    -- | Whether TBB is enabled
  , configTBB :: Bool
  }
  deriving (Read, Show)

defaultExtraConfigFlags :: ExtraConfigFlags
defaultExtraConfigFlags = ExtraConfigFlags [] [] [] True

-- Write custom configure information to a file
writeExtraConfigFile :: ExtraConfigFlags -> IO ()
writeExtraConfigFile config_data =
  rewriteFile extraConfigPath (show config_data)

-- Read custom configure information from a file
readExtraConfigFile :: IO ExtraConfigFlags
readExtraConfigFile =
  evaluate . read =<< readFile extraConfigPath

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

