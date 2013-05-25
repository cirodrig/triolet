
import Prelude hiding(catch)

import Control.Exception
import Control.Monad
import Data.List
import System.Environment
import System.Exit
import System.FilePath
import System.Directory
import System.IO.Error hiding(catch)

import qualified Development.Shake as Shake
import Distribution.ModuleName hiding(main)
import Distribution.PackageDescription
import Distribution.PackageDescription.Parse
           (readPackageDescription)
import Distribution.PackageDescription.Configuration
         (flattenPackageDescription)
import Distribution.Simple
import Distribution.Simple.BuildPaths
import Distribution.Simple.Command
import Distribution.Simple.Configure
  ( getPersistBuildConfig, maybeGetPersistBuildConfig
  , writePersistBuildConfig, checkPersistBuildConfigOutdated)
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.PreProcess
import Distribution.Simple.Program
import Distribution.Simple.Setup hiding(boolOpt)
import Distribution.Simple.Utils
import Distribution.Text
import Distribution.Verbosity

import BuildSystem.Config
import qualified BuildSystem.Command
import qualified BuildSystem.Args
import qualified BuildSystem.Path
import qualified BuildSystem.Rules

gxxProgram = simpleProgram "g++"

-- Remove a file, but recover on error
lenientRemoveFile verb f = removeFile f `catch` check_err 
  where
    check_err e 
      | isDoesNotExistError e = return ()
      | otherwise = 
        let msg = "Could not remove file '" ++ f ++ "':" ++ show e
        in warn verb msg

-------------------------------------------------------------------------------
-- Hooks

-- Build hook: run make
doBuild pkg_desc lbi hooks flags = do
  -- Scan for files and configuration data
  econfig <- readExtraConfigFile

  -- Compile Triolet and the run-time system
  BuildSystem.Rules.shakeWithRules verb lbi econfig $ do
    Shake.want [BuildSystem.Path.trioletFile lbi]
    Shake.want $ BuildSystem.Path.dataFiles lbi

  where
    verb = fromFlag $ buildVerbosity flags

-- | Compile documentation of the compiler's source code
doHaddock pkg_desc lbi hooks flags = withExe pkg_desc $ \exe -> do
  econfig <- readExtraConfigFile

  -- Create output directory
  createDirectoryIfMissingVerbose verb True haddock_dir

  -- Invoke haddock
  sources <- forM (exeModules exe) $ \mod -> do 
    let filename = toFilePath mod `addExtension` ".hs"
    BuildSystem.Path.findInSearchPaths (BuildSystem.Path.trioletSearchPaths lbi) filename

  doc_flags <- BuildSystem.Args.packageDocArgs exe lbi -- Find installed package documentation
  let haddock_args =
        ["-o", haddock_dir, "-h"] ++
        pass_to_ghc (BuildSystem.Args.trioletGhcArgs econfig exe lbi) ++
        doc_flags ++ sources
  rawSystemExit verb "haddock" haddock_args
  where
    verb = fromFlag $ haddockVerbosity flags
    
    -- The directory to hold haddock output
    haddock_dir = haddockPref defaultDistPref pkg_desc

    -- Quote an argument so that it is passed to GHC
    pass_to_ghc opts = BuildSystem.Command.prefixProgArgs "--optghc=" opts
    
doClean orig_clean pkg_desc _lbi hooks flags = do
  let verb = fromFlag $ cleanVerbosity flags
  
  orig_clean pkg_desc _lbi hooks flags

doTest pkg_desc lbi _ flags = do
  econfig <- readExtraConfigFile

  -- compile the test driver
  BuildSystem.Rules.shakeWithRules verb lbi econfig $
    Shake.want [BuildSystem.Path.testDriverFile lbi]

  -- Compute build parameters for the test driver to use when
  -- compiling and linking
  let cc_flags = BuildSystem.Args.targetCompileFlags econfig
      ld_flags = BuildSystem.Args.targetLinkFlags econfig
      
  current_dir <- getCurrentDirectory
  let (host_cc_flags, host_ld_flags) =
        case executables pkg_desc
        of [exe] ->
             (BuildSystem.Args.unitTestCOpts current_dir econfig exe lbi,
              BuildSystem.Args.unitTestLinkOpts current_dir econfig exe lbi)
      
  -- Arguments:
  --   Build directory
  --   Target C compiler flags
  --   Target link flags
  --   Host C compiler flags
  --   Host C linker flags
  let args = fromFlagOrDefault [] $ testList flags
  let test_arguments = [buildDir lbi,
                        show cc_flags,
                        show ld_flags,
                        show host_cc_flags,
                        show host_ld_flags] ++ args
  -- Run the test driver
  rawSystemExit verb (BuildSystem.Path.testDriverFile lbi) test_arguments
  where
    verb = fromFlag $ testVerbosity flags

doConf orig_conf build_info flags = do
  lbi <- orig_conf build_info flags
  
  -- Get information about host architecture
  -- Query search paths from g++
  search_paths <- rawSystemStdout verb "g++" ["-print-search-dirs"]
  lib_paths <- extractGxxLibraryPaths verb search_paths
  host_compile_flags <- identifyHostCFlags verb

  -- Extract extra flags from command line
  custom_flags0 <- case readExtraConfigFlags $ configConfigureArgs flags
                   of Left err -> die err
                      Right x  -> return x

  -- Get information about target architecture 
  target_os <- identifyTargetOS verb
  let custom_flags1 =
        custom_flags0 { configCxxLibDirs = lib_paths
                      , configHostArchFlags = host_compile_flags
                      , configTargetOS = target_os}

  -- Save the GC install prefix to a file
  writeExtraConfigFile custom_flags1

  return lbi
  where
    verb = fromFlagOrDefault normal $ configVerbosity flags

hooks = simpleUserHooks
  { hookedPrograms = gxxProgram :
                     hookedPrograms simpleUserHooks
  , cleanHook = doClean (cleanHook simpleUserHooks)
  , confHook = doConf (confHook simpleUserHooks)
  , buildHook = doBuild
  , testHook = doTest
  , haddockHook = doHaddock
  }

main = defaultMainWithHooks hooks
