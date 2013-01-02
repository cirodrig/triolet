
module SetupSrc.Args where

import Control.Monad
import Data.Maybe
import qualified Development.Shake as Shake
import Distribution.InstalledPackageInfo
import Distribution.PackageDescription
import Distribution.Simple
import Distribution.Simple.GHC
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.PackageIndex
import Distribution.Simple.Utils
import System.Directory
import System.FilePath

import SetupSrc.Path
import SetupSrc.Config
import SetupSrc.Command

-- | Arguments to the Haskell compiler when compiling Triolet
trioletGhcArgs econfig exe lbi =
  let clbi = case lookup "triolet" $ executableConfigs lbi
             of Nothing -> error "Unexpected missing build info"
                Just x -> x
      target = buildDir lbi </> "triolet"
  in ghcOptions lbi (buildInfo exe) clbi target

-- | Extra arguments to the Haskell compiler when compiling Triolet
--   with profiling.  Must compile without profiling first, then compile with
--   these extra arguments.
trioletGhcProfArgs econfig exe lbi =
  ["-prof", "-osuf", "p_o", "-hisuf", "p_hi"]

-- | Arguments to the C compiler when compiling Triolet
trioletCcArgs econfig exe lbi =
  let build_info = buildInfo exe
      includes = prefixIncludePaths $
                 Distribution.PackageDescription.includeDirs build_info
      host_arch_flags = configHostArchFlags econfig
  in host_arch_flags ++ includes

-- | Arguments to the C compiler when compiling the RTS
rtsCcArgs is_cxx econfig exe lbi =
  cc_warning_flags ++ dynamic_flags ++ rts_include_paths ++
  targetCompileFlags econfig
  where
    dynamic_flags = ["-fPIC"]   -- Position-independent code

    rts_include_paths = prefixIncludePaths $ rtsIncludePaths lbi

    cc_warning_flags =
      -- In C, these flags turn some C warnings into errors.
      -- In C++, they're errors by default.
      if is_cxx
      then []
      else ["-Werror", "-Wimplicit-function-declaration", "-Wimplicit-int"]

ifTBB econfig t f = if configTBB econfig then t else f

-- | Argumetns to the low-level Triolet compiler when compiling the RTS
rtsLltArgs econfig lbi = rts_include_paths ++ rts_tbb
  where
    rts_include_paths = prefixIncludePaths $ rtsIncludePaths lbi
    rts_tbb = ifTBB econfig ["-DUSE_TBB"] []

-- | Target-specific compilation flags for C, C++, and llt code. 
targetCompileFlags econfig = target_paths ++ target_tbb
  where
    target_paths = prefixIncludePaths $ configTargetIncludeDirs econfig

    target_tbb = ifTBB econfig ["-DUSE_TBB"] []

targetLinkFlags econfig = "-g" :
                          prefixLibraryPaths target_lib_paths ++
                          prefixLibraries target_libs
  where
    -- Search paths for libraries
    target_lib_paths = configTargetLibDirs econfig ++ configCxxLibDirs econfig
    -- Libraries to link against
    target_libs = ifTBB econfig ["tbb"] [] ++ ["gc", "c", "m", "stdc++"]

-- | GHC arguments to use while building the test driver
testDriverGhcArgs lbi = directories ++ search_paths
  where
    directories =
      ["-odir", testDriverBuildDir lbi, "-hidir", testDriverBuildDir lbi]
    search_paths =
      case testDriverSearchPaths
      of SearchPaths xs -> prefixHaskellPaths xs

-- | C compiler options when building unit tests.
--
--   Unit tests are built with a temporary directory as the working directory,
--   so paths are converted to absolute paths.
unitTestCOpts base_path econfig exe lbi =
  let build_info = buildInfo exe
      includes = prefixIncludePaths $ map (base_path </>) $ Distribution.PackageDescription.includeDirs build_info
      -- TODO: Actually determine whether m32 flag is needed
  in includes

unitTestLinkOpts base_path econfig exe lbi = [] :: [String]

-- | Get flags for installed package documentation.  These are used to create
-- links when building the documentation.
--
-- Find Haddock interface file locations for each package.  Verify that each
-- interface file exists, then add the path as a command line parameter.
packageDocArgs exe lbi = do
  interfaces <- filterM interface_exists haddock_interfaces
  return ["--read-interface=" ++ dir ++ "," ++ path
         | (path, dir) <- interfaces]
  where
    pkg_index = installedPkgs lbi

    interface_exists (iface_path, html_path) = do
      iface_exists <- doesFileExist iface_path
      html_exists <- doesDirectoryExist html_path
      return $ iface_exists && html_exists
    
    -- Haddock interface paths and HTML directory paths of all dependences
    haddock_interfaces =
      [ (iface_path, html_path)
      | (ipid, _)  <- componentPackageDeps $ findExeConfig exe lbi
      , pkg_info   <- maybeToList $ lookupInstalledPackageId pkg_index ipid
      , iface_path <- haddockInterfaces pkg_info
      , html_path  <- haddockHTMLs pkg_info]

