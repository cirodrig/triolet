
import Prelude hiding(catch)

import Control.Exception
import Control.Monad
import Data.List
import Data.Maybe
import System.Environment
import System.Exit
import System.FilePath
import System.Directory
import qualified System.Info
import System.IO.Error hiding(catch)

import Distribution.ModuleName hiding(main)
import Distribution.PackageDescription
import Distribution.PackageDescription.Parse
           (readPackageDescription, readHookedBuildInfo)
import Distribution.PackageDescription.Configuration
         (flattenPackageDescription)
import Distribution.Simple
import Distribution.Simple.Build.PathsModule
import Distribution.Simple.BuildPaths
import Distribution.Simple.Command
import Distribution.Simple.Configure
  ( getPersistBuildConfig, maybeGetPersistBuildConfig
  , writePersistBuildConfig, checkPersistBuildConfig)
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.PreProcess
import Distribution.Simple.Program
import Distribution.Simple.Setup
import Distribution.Simple.Utils
import Distribution.Text
import Distribution.Verbosity

import SetupConfig
import SetupPaths
import SetupMake

makeProgram = simpleProgram "make"
makedependProgram = simpleProgram "makedepend"
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

-- Write the auto-generated 'machine' module
writeMachineModule :: Verbosity 
                   -> LocalBuildInfo
                   -> TargetArchitectureParameters
                   -> IO ()
writeMachineModule verb lbi target = do
  let autogen_dir = autogenModulesDir lbi
      autogen_filename = "Machine.hs"
  
  createDirectoryIfMissingVerbose verb True autogen_dir
  rewriteFile (autogen_dir </> autogen_filename) module_text
  where
    module_text =
      "-- Autogenerated module\n" ++
      "module Machine where\n" ++
      "targetWordSizeBytes :: Int\n" ++
      "targetWordSizeBytes = " ++ show (targetPointerSize target) ++ "\n" ++
      "targetIntSizeBytes :: Int\n" ++
      "targetIntSizeBytes = " ++ show (targetIntSize target) ++ "\n"

-- Write the auto-generated 'machine' header file.
-- The header file is included into both pyasm and c files.
writeMachineHeader :: Verbosity 
                   -> LocalBuildInfo
                   -> TargetArchitectureParameters
                   -> IO ()
writeMachineHeader verb lbi target = do
  let autogen_dir = autogenModulesDir lbi
      autogen_filename = "machine.h"
  
  createDirectoryIfMissingVerbose verb True autogen_dir
  rewriteFile (autogen_dir </> autogen_filename) header_text
  where
    header_text =
      "#ifndef _MACHINE_H_\n" ++
      "#define _MACHINE_H_\n" ++
      "#define WORD_SIZE " ++ show (targetPointerSize target) ++ "\n" ++
      "#define INT_SIZE " ++ show (targetIntSize target) ++ "\n" ++
      "#endif\n"

runMake lbi verbosity args =
  runDbProgram verbosity makeProgram (withPrograms lbi) args

runMakedepend lbi verbosity args =
  runDbProgram verbosity makedependProgram (withPrograms lbi) args

generateDepFile lbi exe verbosity depfile main_path = do
  econfig <- readExtraConfigFile
  rawSystemExit verbosity "ghc" (hsdep_args econfig)
  where
    hsdep_args econfig =
      ["-M", "-dep-makefile", depfile] ++
      pyonGhcOpts econfig exe lbi ++
      [main_path]

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
  target_architecture <- computeTargetArchitectureParameters verb
  writeMachineModule verb lbi target_architecture
  writeMachineHeader verb lbi target_architecture
  preProcess pkg_desc lbi hooks flags
  
  -- Build the executable
  withExe pkg_desc build_exe
  where
    verb = fromFlag $ buildVerbosity flags

    build_exe exe = do
      econfig <- readExtraConfigFile

      -- Generate make rules and variables
      generateCabalMakefile verb econfig exe lbi

      main_path <- findFile (pyonSearchPaths lbi exe) (modulePath exe)

      -- Generate Haskell dependences (without profiling)
      let noprof_lbi = lbi {withProfExe = False}
      generateDepFile noprof_lbi exe verb ".depend_hs.mk" main_path
      
      -- Generate Haskell dependences (with profiling)
      -- If not using profiling, generate an empty file 
      if withProfExe lbi
        then generateDepFile lbi exe verb ".depend_hs_p.mk" main_path
        else writeFile ".depend_hs_p.mk" ""
      
      -- Generate C dependences
      rts_c_files <- mapM (findFile $ rtsSearchPaths lbi) rtsCSourceFiles
      depfile_exists <- doesFileExist ".depend.mk"
      unless depfile_exists $ writeFile ".depend.mk" ""
      let cdep_args =
            ["-f.depend.mk", "-p" ++ rtsBuildDir lbi] ++
            targetCompileFlags econfig ++      -- Preprocessor definitions
            map ("-I" ++) (rtsSearchPaths lbi) ++
            ["-I" ++ "data/include"] ++
            rts_c_files
      runMakedepend lbi verb cdep_args

      -- Run 'make'
      runMake lbi verb ["build"]

-- | Compile documentation of the compiler's source code
doHaddock pkg_desc lbi hooks flags = withExe pkg_desc $ \exe -> do
  econfig <- readExtraConfigFile

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
        pass_to_ghc (pyonGhcOpts econfig exe lbi) ++
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
  econfig <- readExtraConfigFile
      
  -- Generate make rules and variables
  withExe pkg_desc $ \exe -> do generateCabalMakefile verb econfig exe lbi
  
  -- Compile the test driver
  runMake lbi verb [testDriverProgram lbi]
  
  -- Run the test driver
  let cc_flags = targetCompileFlags econfig
      ld_flags = targetLinkFlags econfig
      test_arguments = [buildDir lbi, show cc_flags, show ld_flags] ++ args
  rawSystemExit verb (testDriverProgram lbi) test_arguments

hooks = simpleUserHooks
  { hookedPrograms = gxxProgram : makeProgram : makedependProgram :
                     hookedPrograms simpleUserHooks
  , runTests = doTest
  , cleanHook = doClean (cleanHook simpleUserHooks)
  , buildHook = doBuild
  , haddockHook = doHaddock
  }

customConfigureCommand progs =
  let stdcmd = configureCommand progs -- The command provided by Cabal
      custom_options _ = [include_option, lib_option]
      options mode =
        map (liftOption configStdFlags setConfigStdFlags)
        (commandOptions stdcmd mode) ++
        custom_options mode
      default_flags =
        CustomConfigFlags
        { configExtraFlags = defaultExtraConfigFlags
        , configStdFlags = commandDefaultFlags stdcmd}
  in makeCommand
     (commandName stdcmd)
     (commandSynopsis stdcmd)
     (commandDescription stdcmd)
     default_flags
     options
  where
    include_option, lib_option :: OptionField CustomConfigFlags
    include_option =
      option [] ["extra-target-include-dirs"]
      "An additional include directory to use when compiling pyon code"
      get_extra_include set_extra_include
      (reqArg' "PATH" return id)
    get_extra_include = configTargetIncludeDirs . configExtraFlags
    set_extra_include val flags = modifyConfigExtraFlags flags $ \flags2 ->
      flags2 {configTargetIncludeDirs =
                 val ++ configTargetIncludeDirs flags2}

    lib_option =
      option [] ["extra-target-lib-dirs"]
      "An additional library directory to use when compiling pyon code"
      get_extra_lib set_extra_lib
      (reqArg' "PATH" return id)
    get_extra_lib = configTargetLibDirs . configExtraFlags
    set_extra_lib val flags = modifyConfigExtraFlags flags $ \flags2 ->
      flags2 {configTargetLibDirs =
                 val ++ configTargetLibDirs flags2}

customConfigureAction hooks custom_flags args = do
  configureAction hooks (configStdFlags custom_flags) args
  
  -- Save the GC install prefix to a file
  writeExtraConfigFile (configExtraFlags custom_flags)

-------------------------------------------------------------------------------
-- The following code is copied from Distribution.Simple.  The only difference
-- is that the configure command has been customized to parse extra arguments.
-------------------------------------------------------------------------------

main = do
  args <- getArgs
  topHandler $
    case commandsRun globalCommand commands args of
      CommandHelp   help                 -> printHelp help
      CommandList   opts                 -> printOptionsList opts
      CommandErrors errs                 -> printErrors errs
      CommandReadyToGo (flags, commandParse)  ->
        case commandParse of
          _ | fromFlag (globalVersion flags)        -> printVersion
            | fromFlag (globalNumericVersion flags) -> printNumericVersion
          CommandHelp     help           -> printHelp help
          CommandList     opts           -> printOptionsList opts
          CommandErrors   errs           -> printErrors errs
          CommandReadyToGo action        -> action

  where
    printHelp help = getProgName >>= putStr . help
    printOptionsList = putStr . unlines
    printErrors errs = do
      putStr (concat (intersperse "\n" errs))
      exitWith (ExitFailure 1)
    printNumericVersion = putStrLn $ display cabalVersion
    printVersion        = putStrLn $ "Cabal library version "
                                  ++ display cabalVersion

    progs = addKnownPrograms (hookedPrograms hooks) defaultProgramConfiguration
    commands =
      [customConfigureCommand progs `commandAddAction` customConfigureAction hooks
      ,buildCommand     progs `commandAddAction` buildAction        hooks
      ,installCommand         `commandAddAction` installAction      hooks
      ,copyCommand            `commandAddAction` copyAction         hooks
      ,haddockCommand         `commandAddAction` haddockAction      hooks
      ,cleanCommand           `commandAddAction` cleanAction        hooks
      ,sdistCommand           `commandAddAction` sdistAction        hooks
      ,hscolourCommand        `commandAddAction` hscolourAction     hooks
      ,registerCommand        `commandAddAction` registerAction     hooks
      ,unregisterCommand      `commandAddAction` unregisterAction   hooks
      ,testCommand            `commandAddAction` testAction         hooks
      ]

-- | Combine the preprocessors in the given hooks with the
-- preprocessors built into cabal.
allSuffixHandlers :: UserHooks
                  -> [PPSuffixHandler]
allSuffixHandlers hooks
    = overridesPP (hookedPreProcessors hooks) knownSuffixHandlers
    where
      overridesPP :: [PPSuffixHandler] -> [PPSuffixHandler] -> [PPSuffixHandler]
      overridesPP = unionBy (\x y -> fst x == fst y)

configureAction :: UserHooks -> ConfigFlags -> Args -> IO ()
configureAction hooks flags args = do
    let distPref = fromFlag $ configDistPref flags
    pbi <- preConf hooks args flags

    (mb_pd_file, pkg_descr0) <- confPkgDescr

    --    get_pkg_descr (configVerbosity flags')
    --let pkg_descr = updatePackageDescription pbi pkg_descr0
    let epkg_descr = (pkg_descr0, pbi)

    --(warns, ers) <- sanityCheckPackage pkg_descr
    --errorOut (configVerbosity flags') warns ers

    localbuildinfo0 <- confHook hooks epkg_descr flags

    -- remember the .cabal filename if we know it
    let localbuildinfo = localbuildinfo0{ pkgDescrFile = mb_pd_file }
    writePersistBuildConfig distPref localbuildinfo

    let pkg_descr = localPkgDescr localbuildinfo
    postConf hooks args flags pkg_descr localbuildinfo
  where
    verbosity = fromFlag (configVerbosity flags)
    confPkgDescr :: IO (Maybe FilePath, GenericPackageDescription)
    confPkgDescr = do
      mdescr <- readDesc hooks
      case mdescr of
        Just descr -> return (Nothing, descr)
        Nothing -> do
          pdfile <- defaultPackageDesc verbosity
          descr  <- readPackageDescription verbosity pdfile
          return (Just pdfile, descr)

buildAction :: UserHooks -> BuildFlags -> Args -> IO ()
buildAction hooks flags args = do
  let distPref  = fromFlag $ buildDistPref flags
      verbosity = fromFlag $ buildVerbosity flags

  lbi <- getBuildConfig hooks distPref
  progs <- reconfigurePrograms verbosity
             (buildProgramPaths flags)
             (buildProgramArgs flags)
             (withPrograms lbi)

  hookedAction preBuild buildHook postBuild
               (return lbi { withPrograms = progs })
               hooks flags args

hscolourAction :: UserHooks -> HscolourFlags -> Args -> IO ()
hscolourAction hooks flags args
    = do let distPref = fromFlag $ hscolourDistPref flags
         hookedAction preHscolour hscolourHook postHscolour
                      (getBuildConfig hooks distPref)
                      hooks flags args

haddockAction :: UserHooks -> HaddockFlags -> Args -> IO ()
haddockAction hooks flags args = do
  let distPref  = fromFlag $ haddockDistPref flags
      verbosity = fromFlag $ haddockVerbosity flags

  lbi <- getBuildConfig hooks distPref
  progs <- reconfigurePrograms verbosity
             (haddockProgramPaths flags)
             (haddockProgramArgs flags)
             (withPrograms lbi)

  hookedAction preHaddock haddockHook postHaddock
               (return lbi { withPrograms = progs })
               hooks flags args

cleanAction :: UserHooks -> CleanFlags -> Args -> IO ()
cleanAction hooks flags args = do
                pbi <- preClean hooks args flags

                pdfile <- defaultPackageDesc verbosity
                ppd <- readPackageDescription verbosity pdfile
                let pkg_descr0 = flattenPackageDescription ppd
                let pkg_descr = updatePackageDescription pbi pkg_descr0

                cleanHook hooks pkg_descr () hooks flags
                postClean hooks args flags pkg_descr ()
  where verbosity = fromFlag (cleanVerbosity flags)

copyAction :: UserHooks -> CopyFlags -> Args -> IO ()
copyAction hooks flags args
    = do let distPref = fromFlag $ copyDistPref flags
         hookedAction preCopy copyHook postCopy
                      (getBuildConfig hooks distPref)
                      hooks flags args

installAction :: UserHooks -> InstallFlags -> Args -> IO ()
installAction hooks flags args
    = do let distPref = fromFlag $ installDistPref flags
         hookedAction preInst instHook postInst
                      (getBuildConfig hooks distPref)
                      hooks flags args

sdistAction :: UserHooks -> SDistFlags -> Args -> IO ()
sdistAction hooks flags args = do
                let distPref = fromFlag $ sDistDistPref flags
                pbi <- preSDist hooks args flags

                mlbi <- maybeGetPersistBuildConfig distPref
                pdfile <- defaultPackageDesc verbosity
                ppd <- readPackageDescription verbosity pdfile
                let pkg_descr0 = flattenPackageDescription ppd
                let pkg_descr = updatePackageDescription pbi pkg_descr0

                sDistHook hooks pkg_descr mlbi hooks flags
                postSDist hooks args flags pkg_descr mlbi
  where verbosity = fromFlag (sDistVerbosity flags)

testAction :: UserHooks -> TestFlags -> Args -> IO ()
testAction hooks flags args = do
                let distPref = fromFlag $ testDistPref flags
                localbuildinfo <- getBuildConfig hooks distPref
                let pkg_descr = localPkgDescr localbuildinfo
                runTests hooks args False pkg_descr localbuildinfo

registerAction :: UserHooks -> RegisterFlags -> Args -> IO ()
registerAction hooks flags args
    = do let distPref = fromFlag $ regDistPref flags
         hookedAction preReg regHook postReg
                      (getBuildConfig hooks distPref)
                      hooks flags args

unregisterAction :: UserHooks -> RegisterFlags -> Args -> IO ()
unregisterAction hooks flags args
    = do let distPref = fromFlag $ regDistPref flags
         hookedAction preUnreg unregHook postUnreg
                      (getBuildConfig hooks distPref)
                      hooks flags args

hookedAction :: (UserHooks -> Args -> flags -> IO HookedBuildInfo)
        -> (UserHooks -> PackageDescription -> LocalBuildInfo
                      -> UserHooks -> flags -> IO ())
        -> (UserHooks -> Args -> flags -> PackageDescription
                      -> LocalBuildInfo -> IO ())
        -> IO LocalBuildInfo
        -> UserHooks -> flags -> Args -> IO ()
hookedAction pre_hook cmd_hook post_hook get_build_config hooks flags args = do
   pbi <- pre_hook hooks args flags
   localbuildinfo <- get_build_config
   let pkg_descr0 = localPkgDescr localbuildinfo
   --pkg_descr0 <- get_pkg_descr (get_verbose flags)
   let pkg_descr = updatePackageDescription pbi pkg_descr0
   -- XXX: should we write the modified package descr back to the
   -- localbuildinfo?
   cmd_hook hooks pkg_descr localbuildinfo hooks flags
   post_hook hooks args flags pkg_descr localbuildinfo

getBuildConfig :: UserHooks -> FilePath -> IO LocalBuildInfo
getBuildConfig hooks distPref = do
  lbi <- getPersistBuildConfig distPref
  case pkgDescrFile lbi of
    Nothing -> return ()
    Just pkg_descr_file -> checkPersistBuildConfig distPref pkg_descr_file
  return lbi {
    withPrograms = restoreProgramConfiguration
                     (builtinPrograms ++ hookedPrograms hooks)
                     (withPrograms lbi)
  }

-- End of code from Distribution.Simple
-------------------------------------------------------------------------------
