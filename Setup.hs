
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

{-
-- | Generate a rule to compile a .hs file
--
-- > D/A/B.o : E/A/B.hs
-- > 	mkdir -p D
-- > 	$(HC) -c $< $(PYON_HS_C_OPTS)
-- > 	touch D/A/B.hi
compileHsFile :: FilePath       -- ^ Build path
              -> ModuleName     -- ^ Module to compile
              -> FilePath       -- ^ Source file
              -> MakeRule
compileHsFile build_path mod src =
  let o_file = build_path </> toFilePath mod `addExtension` ".o"
      o_path = takeDirectory o_file
      hi_file = build_path </> toFilePath mod `addExtension` ".hi"
  in MakeRule o_file [src] $
     "mkdir -p " ++ o_path ++ "\n\
     \$(HC) -c $< $(PYON_HS_C_OPTS)\n\
     \touch " ++ hi_file

-- | Generate a rule to compile a .hs-boot file
--
-- > D/A/B.o-boot : E/A/B.hs-boot
-- > 	mkdir -p D
-- > 	$(HC) -c $< $(PYON_HS_C_OPTS)
compileHsBootFile :: FilePath       -- ^ Build directory
                  -> ModuleName     -- ^ Module to compile
                  -> FilePath       -- ^ Source file
                  -> MakeRule
compileHsBootFile build_path mod src =
  let o_file = build_path </> toFilePath mod `addExtension` ".o-boot"
      o_path = takeDirectory o_file
  in MakeRule o_file [src] $
     "mkdir -p " ++ o_path ++ "\n\
     \$(HC) -c $< $(PYON_HS_C_OPTS)"

compileRtsFile :: FilePath
               -> FilePath
               -> FilePath
               -> MakeRule
compileRtsFile build_path source_path src =
  let o_file = build_path </> src `replaceExtension` ".o"
      i_file = source_path </> src
  in MakeRule o_file [i_file] $
     "mkdir -p " ++ takeDirectory o_file ++ "\n\
     \$(CC) -c $< -o $@ $(RTS_C_C_OPTS)"
-}

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

runMake lbi flags args =
  let verb = fromFlag $ buildVerbosity flags  
  in runDbProgram verb makeProgram (withPrograms lbi) args

-------------------------------------------------------------------------------
-- Hooks

-- Pre-build hook: Run 'alex'
preProcess pkg_desc lbi hooks flags = withExe pkg_desc $ \exe -> do
  lex_alexpath <-
    findFile (pyonSearchPaths lbi exe) $ lex_module `addExtension` ".x"
  
  -- Create output directory
  createDirectoryIfMissingVerbose verb True (dropFileName lex_hspath)

  -- Is target out of date?
  out_of_date <- lex_hspath `olderThan` [lex_alexpath]
  
  -- Run lexer
  let alex = ppAlex (buildInfo exe) lbi
  when out_of_date $ runSimplePreProcessor alex lex_alexpath lex_hspath verb

  where
    verb = fromFlag $ buildVerbosity flags
    autogen_dir = autogenModulesDir lbi
    lex_module = "LLParser" </> "Lexer"
    lex_hspath = autogen_dir </> lex_module `addExtension` ".hs"
  

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
      let include_args =    
            ["-i" ++ path | path <- pyonSearchPaths lbi exe]
          hsdep_args =
            ["-M", "-dep-makefile", ".depend_hs.mk",
             "-odir", pyonBuildDir lbi,
             "-hidir", pyonBuildDir lbi] ++ include_args ++
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
      runMake lbi flags ["build"]

doClean orig_clean pkg_desc _lbi hooks flags = do
  let verb = fromFlag $ cleanVerbosity flags
  lenientRemoveFile verb cabalMakeFile
  
  orig_clean pkg_desc _lbi hooks flags

hooks = autoconfUserHooks
  { hookedPrograms = makeProgram : hookedPrograms autoconfUserHooks
  , cleanHook = doClean (cleanHook autoconfUserHooks)
  , buildHook = doBuild
  }

main = defaultMainWithHooks hooks
