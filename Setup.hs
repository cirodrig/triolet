
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

import SetupSrc.Config
import qualified SetupSrc.Command
import qualified SetupSrc.Args
import qualified SetupSrc.Path
import qualified SetupSrc.Rules

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

{-
-- Preprocessing before build
preProcess pkg_desc lbi hooks flags = withExe pkg_desc $ \exe -> do
  ppRunAlex exe $ "LLParser" </> "Lexer"
  ppRunAlex exe $ "CParser2" </> "Lexer"
  ppRunAlex exe $ "Language" </> "Python" </> "Version3" </> "Parser" </> "Lexer"
  ppRunHappy exe $ "Language" </> "Python" </> "Version3" </> "Parser" </> "Parser"
  ppRunHsc exe $ "CxxInterface" </> "SignatureHS"
  where
    verb = fromFlag $ buildVerbosity flags
    autogen_dir = autogenModulesDir lbi
    
    ppRunHappy exe path = do
      -- Find paths to input and output files
      let hspath = autogen_dir </> path `addExtension` ".hs"
      ypath <- findFile (trioletSearchPaths lbi exe) $ path `addExtension` ".y"
  
      -- Create output directory
      createDirectoryIfMissingVerbose verb True (dropFileName hspath)

      -- Is target out of date?
      out_of_date <- hspath `olderThan` [ypath]
  
      -- Run parser generator
      let happy = ppHappy (buildInfo exe) lbi
      when out_of_date $ runSimplePreProcessor happy ypath hspath verb
    
    ppRunAlex exe path = do
      -- Find paths to input and output files
      let hspath = autogen_dir </> path `addExtension` ".hs"
      alexpath <- findFile (trioletSearchPaths lbi exe) $ path `addExtension` ".x"
  
      -- Create output directory
      createDirectoryIfMissingVerbose verb True (dropFileName hspath)

      -- Is target out of date?
      out_of_date <- hspath `olderThan` [alexpath]
  
      -- Run lexer
      let alex = ppAlex (buildInfo exe) lbi
      when out_of_date $ runSimplePreProcessor alex alexpath hspath verb

    ppRunHsc exe path = do
      -- Find paths to input and output files
      let hspath = autogen_dir </> path `addExtension` ".hs"
      hscpath <- findFile (trioletSearchPaths lbi exe) $ path `addExtension` ".hsc"
      -- Create output directory
      createDirectoryIfMissingVerbose verb True (dropFileName hspath)

      -- Is target out of date?
      out_of_date <- hspath `olderThan` [hscpath]
  
      -- Run lexer
      let hsc = ppHsc2hs (buildInfo exe) lbi
      when out_of_date $ runSimplePreProcessor hsc hscpath hspath verb
-}

-- Build hook: run make
doBuild pkg_desc lbi hooks flags = do
  -- Scan for files and configuration data
  econfig <- readExtraConfigFile

  -- Compile Triolet and the run-time system
  SetupSrc.Rules.shakeWithRules verb lbi econfig $ do
    Shake.want [SetupSrc.Path.trioletFile lbi]
    Shake.want $ SetupSrc.Path.dataFiles lbi

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
    SetupSrc.Path.findInSearchPaths (SetupSrc.Path.trioletSearchPaths lbi) filename

  doc_flags <- SetupSrc.Args.packageDocArgs exe lbi -- Find installed package documentation
  let haddock_args =
        ["-o", haddock_dir, "-h"] ++
        pass_to_ghc (SetupSrc.Args.trioletGhcArgs econfig exe lbi) ++
        doc_flags ++ sources
  rawSystemExit verb "haddock" haddock_args
  where
    verb = fromFlag $ haddockVerbosity flags
    
    -- The directory to hold haddock output
    haddock_dir = haddockPref defaultDistPref pkg_desc

    -- Quote an argument so that it is passed to GHC
    pass_to_ghc opts = SetupSrc.Command.prefixProgArgs "--optghc=" opts
    
doClean orig_clean pkg_desc _lbi hooks flags = do
  let verb = fromFlag $ cleanVerbosity flags
  
  orig_clean pkg_desc _lbi hooks flags

doTest args _ pkg_desc lbi flags = do
  econfig <- readExtraConfigFile

  -- compile the test driver
  SetupSrc.Rules.shakeWithRules verb lbi econfig $
    Shake.want [SetupSrc.Path.testDriverFile lbi]

  -- Compute build parameters for the test driver to use when
  -- compiling and linking
  let cc_flags = SetupSrc.Args.targetCompileFlags econfig
      ld_flags = SetupSrc.Args.targetLinkFlags econfig
      
  current_dir <- getCurrentDirectory
  let (host_cc_flags, host_ld_flags) =
        case executables pkg_desc
        of [exe] ->
             (SetupSrc.Args.unitTestCOpts current_dir econfig exe lbi,
              SetupSrc.Args.unitTestLinkOpts current_dir econfig exe lbi)
      
  -- Arguments:
  --   Build directory
  --   Target C compiler flags
  --   Target link flags
  --   Host C compiler flags
  --   Host C linker flags
  let test_arguments = [buildDir lbi,
                        show cc_flags,
                        show ld_flags,
                        show host_cc_flags,
                        show host_ld_flags] ++ args
  -- Run the test driver
  rawSystemExit verb (SetupSrc.Path.testDriverFile lbi) test_arguments
  where
    verb = fromFlag $ testVerbosity flags

hooks = simpleUserHooks
  { hookedPrograms = gxxProgram :
                     hookedPrograms simpleUserHooks
  , cleanHook = doClean (cleanHook simpleUserHooks)
  , buildHook = doBuild
  , haddockHook = doHaddock
  }

customConfigureCommand progs =
  let stdcmd = configureCommand progs -- The command provided by Cabal
      custom_options _ = [include_option, lib_option, tbb_option]
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
    include_option, lib_option, tbb_option :: OptionField CustomConfigFlags
    tbb_option =
      option [] ["tbb"]
      "parallel execution using the Threading Building Blocks library"
      get_tbb set_tbb (boolOpt return id [] [])
    get_tbb = configTBB . configExtraFlags
    set_tbb val flags = modifyConfigExtraFlags flags $ \flags2 ->
      flags2 {configTBB = val}

    include_option =
      option [] ["extra-target-include-dirs"]
      "An additional include directory to use when compiling triolet code"
      get_extra_include set_extra_include
      (reqArg' "PATH" return id)
    get_extra_include = configTargetIncludeDirs . configExtraFlags
    set_extra_include val flags = modifyConfigExtraFlags flags $ \flags2 ->
      flags2 {configTargetIncludeDirs =
                 val ++ configTargetIncludeDirs flags2}

    lib_option =
      option [] ["extra-target-lib-dirs"]
      "An additional library directory to use when compiling triolet code"
      get_extra_lib set_extra_lib
      (reqArg' "PATH" return id)
    get_extra_lib = configTargetLibDirs . configExtraFlags
    set_extra_lib val flags = modifyConfigExtraFlags flags $ \flags2 ->
      flags2 {configTargetLibDirs =
                 val ++ configTargetLibDirs flags2}

customConfigureAction hooks custom_flags args = do
  configureAction hooks (configStdFlags custom_flags) args
  
  let verb = fromFlagOrDefault normal $
             configVerbosity $ configStdFlags custom_flags

  -- Query search paths from g++
  search_paths <- rawSystemStdout verb "g++" ["-print-search-dirs"]
  lib_paths <- extractGxxLibraryPaths verb search_paths

  -- Identify extra C/C++ host compile flags
  host_compile_flags <- identifyHostCFlags verb
  
  let custom_flags1 =
        modifyConfigExtraFlags custom_flags $
        \f -> f { configCxxLibDirs = lib_paths
                , configHostArchFlags = host_compile_flags}

  -- Save the GC install prefix to a file
  writeExtraConfigFile (configExtraFlags custom_flags1)

-------------------------------------------------------------------------------
-- The following code is copied from Distribution.Simple.  The only difference
-- is that the configure and test commands have been customized to parse extra
-- arguments and to pass extra information.
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
                -- Override with our own test code
                doTest args False pkg_descr localbuildinfo flags

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
    Just pkg_descr_file -> do
      outdated <- checkPersistBuildConfigOutdated distPref pkg_descr_file
      when outdated $
        die "Configuration file has changed; please reconfigure."
  return lbi {
    withPrograms = restoreProgramConfiguration
                     (builtinPrograms ++ hookedPrograms hooks)
                     (withPrograms lbi)
  }

-- End of code from Distribution.Simple
-------------------------------------------------------------------------------
