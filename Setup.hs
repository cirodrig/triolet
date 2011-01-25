
import Prelude hiding(catch)

import Control.Exception
import Control.Monad
import Data.List
import Data.Maybe
import System.FilePath
import System.Directory
import System.IO.Error hiding(catch)

import Distribution.ModuleName hiding(main)
import Distribution.PackageDescription
import Distribution.Simple
import Distribution.Simple.Build.PathsModule
import Distribution.Simple.BuildPaths
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.PreProcess
import Distribution.Simple.Program
import Distribution.Simple.Setup
import Distribution.Simple.Utils
import Distribution.Verbosity

import SetupPaths
import SetupMake

makeProgram = simpleProgram "make"
gxxProgram = simpleProgram "g++"

-- Remove a file, but recover on error
lenientRemoveFile verb f = removeFile f `catch` check_err 
  where
    check_err e 
      | isDoesNotExistError e = return ()
      | otherwise = 
        let msg = "Could not remove file '" ++ f ++ "':" ++ show e
        in warn verb msg

-- Write the auto-generated 'paths' module
writePathsModule verb pkg_desc lbi = do
  let paths_module =
        Distribution.Simple.Build.PathsModule.generate pkg_desc lbi
      autogen_dir = autogenModulesDir lbi
      autogen_filename =
        toFilePath (autogenModuleName pkg_desc) `addExtension` ".hs"

  createDirectoryIfMissingVerbose verb True autogen_dir
  rewriteFile (autogen_dir </> autogen_filename) paths_module

runMake lbi verbosity args =
  runDbProgram verbosity makeProgram (withPrograms lbi) args

-------------------------------------------------------------------------------
-- Hooks

-- Preprocessing before build
preProcess pkg_desc lbi hooks flags = withExe pkg_desc $ \exe -> do
  ppRunAlex exe $ "LLParser" </> "Lexer"
  ppRunAlex exe $ "CParser" </> "Lexer"
  where
    verb = fromFlag $ buildVerbosity flags
    autogen_dir = autogenModulesDir lbi
    
    ppRunAlex exe path = do
      -- Find paths to input and output files
      let hspath = autogen_dir </> path `addExtension` ".hs"
      alexpath <- findFile (pyonSearchPaths lbi exe) $ path `addExtension` ".x"
  
      -- Create output directory
      createDirectoryIfMissingVerbose verb True (dropFileName hspath)

      -- Is target out of date?
      out_of_date <- hspath `olderThan` [alexpath]
  
      -- Run lexer
      let alex = ppAlex (buildInfo exe) lbi
      when out_of_date $ runSimplePreProcessor alex alexpath hspath verb

-- Build hook: run make
doBuild pkg_desc lbi hooks flags = do
  -- Generate modules if they don't alredy exist
  writePathsModule verb pkg_desc lbi
  preProcess pkg_desc lbi hooks flags
  
  -- Build the executable
  withExe pkg_desc build_exe
  where
    verb = fromFlag $ buildVerbosity flags

    build_exe exe = do
      -- Generate make rules and variables
      generateCabalMakefile verb exe lbi

      -- Generate Haskell dependences
      main_path <- findFile (pyonSearchPaths lbi exe) (modulePath exe)
      let hsdep_args =
            ["-M", "-dep-makefile", ".depend_hs.mk"] ++
            targetFlags ++
            pyonGhcPathFlags exe lbi ++
            [main_path]
      
      rawSystemExit verb "ghc" hsdep_args

      -- Generate C dependences
      rts_c_files <- mapM (findFile $ rtsSearchPaths lbi) rtsCSourceFiles
      depfile_exists <- doesFileExist ".depend.mk"
      unless depfile_exists $ writeFile ".depend.mk" ""
      let cdep_args =
            ["-f.depend.mk", "-p" ++ rtsBuildDir lbi] ++
            map ("-I" ++) (rtsSearchPaths lbi) ++
            ["-I" ++ "data/include"] ++
            rts_c_files
      rawSystemExit verb "makedepend" cdep_args

      -- Run 'make'
      runMake lbi verb ["build"]

-- | Compile documentation of the compiler's source code
doHaddock pkg_desc lbi hooks flags = withExe pkg_desc $ \exe -> do
  -- Create output directory
  createDirectoryIfMissingVerbose verb True haddock_dir

  -- Invoke haddock
  sources <- forM (exeModules exe) $ \mod -> do 
    let filename = toFilePath mod `addExtension` ".hs"
    path <- findFilePath' (pyonSearchPaths lbi exe) filename
    return $ path </> filename

  doc_flags <- packageDocFlags exe lbi -- Find installed package documentation
  let haddock_args =
        ["-o", haddock_dir, "-h"] ++
        pass_to_ghc (pyonGhcOpts exe lbi) ++
        doc_flags ++ sources
  rawSystemExit verb "haddock" haddock_args
  where
    verb = fromFlag $ haddockVerbosity flags
    
    -- The directory to hold haddock output
    haddock_dir = haddockPref defaultDistPref pkg_desc

    -- Quote an argument so that it is passed to GHC
    pass_to_ghc opts = ["--optghc=" ++ opt | opt <- opts]
    
doClean orig_clean pkg_desc _lbi hooks flags = do
  let verb = fromFlag $ cleanVerbosity flags
  lenientRemoveFile verb cabalMakeFile
  
  orig_clean pkg_desc _lbi hooks flags

doTest args _ pkg_desc lbi = do
  let verb = normal
  -- Generate make rules and variables
  withExe pkg_desc $ \exe -> do generateCabalMakefile verb exe lbi
  
  -- Compile the test driver
  runMake lbi verb [testDriverProgram lbi]
  
  -- Run the test driver
  let flag_32 = if force32BitCompilation then ["-m32"] else []
      cc_flags = flag_32
      ld_flags = flag_32
      test_arguments = [buildDir lbi, show cc_flags, show ld_flags]
  rawSystemExit verb (testDriverProgram lbi) test_arguments

hooks = simpleUserHooks
  { hookedPrograms = gxxProgram : makeProgram : hookedPrograms simpleUserHooks
  , runTests = doTest
  , cleanHook = doClean (cleanHook simpleUserHooks)
  , buildHook = doBuild
  , haddockHook = doHaddock
  }

main = defaultMainWithHooks hooks
