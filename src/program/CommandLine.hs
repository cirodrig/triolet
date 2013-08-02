{-| Command line parsing.

The exported function, 'parseCommandLineArguments', interprets the program's 
command line.  If the command line is ill-formed, or the given command is to
print a help message, it will print messages and end the program.  Otherwise
it will return a 'Job' describing the actions to perform.

The command line is first parsed into individual options with 'getOpt'.  Then
the options are processed one at a time, and the result is turned into a 'Job'.
-}

module CommandLine(CommandLineGlobals(..), parseCommandLineArguments)
where

import Control.Monad
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import System.Console.GetOpt
import System.Environment
import System.FilePath
import System.IO

import Paths
import Job

-- | An action to be taken 
data Action =
    GetUsage                    -- ^ Show a usage string
  | GetHelp                     -- ^ Get help documentation
  | GenerateBuiltinLibrary      -- ^ Generate object code of the
                                --   built-in library
  | CompileObject               -- ^ Compile to object code
  | ConflictingAction           -- ^ Conflicting options given
    deriving(Eq)

-- | Priority of an action.  Higher-priority actions override lower-priority
-- actions.
actionPriority :: Action -> Int
actionPriority GetUsage = 0
actionPriority GetHelp = 10
actionPriority GenerateBuiltinLibrary = 1
actionPriority CompileObject = 1
actionPriority ConflictingAction = 11

-- | A language to process
data Language =
    NoneLanguage                -- ^ Infer language based on file extension
  | TrioletLanguage             -- ^ Triolet code
  | LLTrioletLanguage           -- ^ Low-level Triolet code
    deriving(Eq)

-- | A command-line option modifies the option interpreter state
newtype Opt = Opt (InterpretOptsState -> InterpretOptsState)

instance Monoid Opt where
  mempty = Opt id
  Opt f `mappend` Opt g = Opt (g . f)

generateBuiltinLibraryCommandName = "generate-builtin-library"

optionDescrs =
  [ Option "h" ["help"] (NoArg (Opt $ setAction GetHelp))
    "display usage information"
  , Option "" ["keep-c-files"] (NoArg (Opt setKeepCFiles)) 
    "save generated C files in output directory"
  , Option "x" [] (ReqArg (\lang -> Opt $ setLanguage lang) "LANG")
    ("specify input language\n" ++
     "(options are 'none', 'triolet', 'lltriolet')")
  , Option "o" [] (ReqArg (\file -> Opt $ setOutput file) "FILE")
    "specify output file"
  , Option "D" [] (ReqArg (\mac -> Opt $ addMacro mac) "MACRO")
    "define a preprocessor macro; ignored when compiling triolet files"
  , Option "I" [] (ReqArg (\mac -> Opt $ addIncludePath mac) "PATH")
    "add a path to the include search path; ignored when compiling triolet files"
  , Option "f" [] (ReqArg (Opt . addFlag) "FLAG")
    "enable/disable a compiler flag"
  , Option "" ["fuel"] (ReqArg (\fuel -> Opt $ setFuel fuel) "FUEL")
    "limit the number of optimizations applied"
  , Option "" [generateBuiltinLibraryCommandName]
    (NoArg (Opt $ setAction GenerateBuiltinLibrary))
    "generate object code of the built-in library"
  ]

-- | Parse command-line arguments.  Return some global variable values and 
--   a job to perform.
--
--   If parsing encounters an error, the do-nothing job is returned.
parseCommandLineArguments :: IO (CommandLineGlobals, Job ())
parseCommandLineArguments = do
  raw_args <- getArgs
  let args = snd $ splitDataFilePath raw_args
  let (options, _, errors) =
        getOpt (ReturnInOrder (\file -> Opt $ addFile file)) optionDescrs args

  -- Print errors or create a job
  if not $ null errors
    then do mapM_ putStrLn errors
            return (defaultCommandLineGlobals, pass)
    else interpretOptions options

usageHeader = do
  program <- getProgName
  let usage = "Usage: " ++ program ++ " [OPTION...] files..."
  return usage

-------------------------------------------------------------------------------
-- Interpret command-line options

interpretOptions :: [Opt] -> IO (CommandLineGlobals, Job ())
interpretOptions opts =
  let commands = case mconcat opts of Opt f -> f initialState
  in case reverse $ interpreterErrors commands
     of xs@(_:_) -> do mapM_ (hPutStrLn stderr) xs
                       return (defaultCommandLineGlobals, pass)
        [] -> do
          commands' <- postProcessCommands commands
          case currentAction commands' of
            GetUsage -> do
              -- Print brief usage info and exit
              header <- usageHeader
              putStrLn header
              putStrLn "For usage information, invoke with --help"
              do_nothing
            GetHelp -> do
              -- Print usage info and exist
              header <- usageHeader
              putStrLn $ usageInfo header optionDescrs
              do_nothing
            GenerateBuiltinLibrary 
              | not $ null (inputFiles commands') -> do
                  hPutStrLn stderr ("Input files cannot be specified with --" ++ generateBuiltinLibraryCommandName)
                  do_nothing
              | otherwise -> do
                  let output = outputFile commands'
                  job <- compileBuiltinLibraryJob commands' output
                  return (mkCommandLineGlobals commands', job)
            CompileObject -> do
              let inputs = reverse $ inputFiles commands'
                  output = outputFile commands'
              
              job <- compileObjectsJob commands' inputs output
              return (mkCommandLineGlobals commands', job)
            ConflictingAction -> do
              hPutStrLn stderr "Conflicting commands given on command line"
              hPutStrLn stderr "For usage information, invoke with --help"
              do_nothing
  where
    do_nothing = return (defaultCommandLineGlobals, pass)

-- | After reading all options, update some parts of the interpreted state
--   based on the presence/absence of options
postProcessCommands commands = do
  input_languages <- mapM chooseLanguage $ inputFiles commands
  let action =
        -- If no action was specified and there's at least one input file,
        -- default to 'CompileObject'
        case currentAction commands
        of GetUsage | not $ null (inputFiles commands) -> CompileObject
           x -> x
      need_core_ir =
        -- If generating the builtin library or compiling a Triolet file, the
        -- core builtin module must be loaded
        currentNeedCoreIR commands ||
        currentAction commands == GenerateBuiltinLibrary ||
        any (TrioletLanguage ==) input_languages

  let commands' = commands { currentNeedCoreIR = need_core_ir
                           , currentAction = action}
  return commands'

-- | Global variable values that were given on the command line.
--   These are returned
data CommandLineGlobals =
  CommandLineGlobals
  { -- | Initial value of fuel used by the simplifier
    initValueForFuel :: !Int

    -- | Whether the core IR is used in this execution of the compiler.
    --   Backend-only compilation doesn't use the core IR.
  , useCoreIR :: !Bool
  }

defaultCommandLineGlobals =
  CommandLineGlobals
  { initValueForFuel = -1
  , useCoreIR = False
  }

mkCommandLineGlobals :: InterpretOptsState -> CommandLineGlobals
mkCommandLineGlobals st =
  CommandLineGlobals
  { initValueForFuel = fromMaybe (-1) $ currentFuel st
  , useCoreIR = currentNeedCoreIR st
  }


data InterpretOptsState =
  InterpretOptsState
  { currentAction :: !Action 
  , currentLanguage :: !Language
  , outputFile :: Maybe String
    -- | Do we save temporary C files?
  , keepCFiles :: !Bool
    -- | List of input files and languages, in /reverse/ order
  , inputFiles :: [(String, Language)]
    -- | List of error messages, in /reverse/ order
  , interpreterErrors :: [String]
    -- | List of preprocessor macros
  , ppMacros :: [(String, Maybe String)]
    -- | List of include search paths, in /reverse/ order
  , includeSearchPaths :: [String]
    -- | Set of boolean compilation settings chosen with \"-f\"
  , commandLineFlags :: CompileFlags
    -- | Amount of fuel
  , currentFuel :: !(Maybe Int)
    -- | Whether core IR is needed
  , currentNeedCoreIR :: !Bool
  }

initialState = InterpretOptsState { currentAction = GetUsage
                                  , currentLanguage = NoneLanguage
                                  , outputFile = Nothing
                                  , keepCFiles = False
                                  , inputFiles = []
                                  , interpreterErrors = []
                                  , ppMacros = []
                                  , includeSearchPaths = []
                                  , commandLineFlags =
                                      -- Some flags are enabled by default 
                                      Set.fromList [DoParallelization]
                                  , currentFuel = Nothing
                                  , currentNeedCoreIR = False
                                  }

putError st e = st {interpreterErrors = e : interpreterErrors st}

setKeepCFiles st = st {keepCFiles = True}

setAction new st =
  case actionPriority old `compare` actionPriority new
  of GT -> update_action old
     LT -> update_action new
     EQ | old == new -> update_action new
        | otherwise  -> update_action ConflictingAction
  where
    old = currentAction st
    update_action a = st {currentAction = a}

setLanguage lang_string st =
  case language
  of Just l  -> st {currentLanguage = l}
     Nothing -> putError st $ "Unrecognized language: " ++ lang_string
  where
    language = lookup lang_string
               [ ("none", NoneLanguage)
               , ("triolet", TrioletLanguage)
               , ("lltriolet", LLTrioletLanguage)
               ]

setFuel fuel_string st =
  case reads fuel_string
  of (f, "") : _ | f >= 0 -> st {currentFuel = Just f}
     _ -> putError st "Fuel must be a positive integer"

addMacro mac st =
  let macro =
        case break ('=' ==) mac
        of (name, '=':value) -> (name, Just value)
           (name, []) -> (name, Nothing)
  in st {ppMacros = macro : ppMacros st}

addIncludePath path st =
  st {includeSearchPaths = path : includeSearchPaths st}

addFlag flagname st =
  let (negated, base_flagname) =
        case flagname
        of 'n':'o':'-':neg_flagname -> (True, neg_flagname)
           _ -> (False, flagname)
  in case lookup base_flagname flag_names
     of Nothing  -> putError st $ "Unrecognized flag: " ++ show flagname
        Just flg ->
          let update_flag =
                if negated then Set.delete flg else Set.insert flg
          in st {commandLineFlags = update_flag $ commandLineFlags st}
  where
    flag_names :: [(String, CompileFlag)]
    flag_names = [("parallelize", DoParallelization)]

setOutput file st =
  case outputFile st of
    Nothing -> st {outputFile = Just file}
    Just _  -> putError st $ "Only one output file may be given"

addFile file st =
  let lang = currentLanguage st
  in st { inputFiles = (file, lang) : inputFiles st}

-------------------------------------------------------------------------------
-- Job creation

chooseLanguage :: (String, Language) -> IO Language
chooseLanguage (file_path, NoneLanguage) = from_suffix file_path
  where
    from_suffix path
      | takeExtension path == ".tri" = return TrioletLanguage
      | takeExtension path == ".llt" = return LLTrioletLanguage
      | otherwise = let msg = "Cannot determine language of '" ++ path ++ "'"
                    in fail msg

chooseLanguage (_, lang) = return lang

compileBuiltinLibraryJob config Nothing = do
  hPutStrLn stderr "Must specify output file"
  return pass

compileBuiltinLibraryJob config (Just output_path) = do
  iface_files <- findInterfaceFiles False
  let ifile = writeFileFromPath $ ifacePath output_path
      outfile = writeFileFromPath output_path
  compileWithCFile config output_path $
    return $ \cfile -> builtinLibraryCompilation
                           (commandLineFlags config) iface_files
                           cfile ifile outfile

-- | Compile one or many object files
compileObjectsJob config [] output = do
  hPutStrLn stderr "No input files"
  return pass

compileObjectsJob config [input] output =
  -- Allow overriding the output file name when one input file is given
  compileObjectJob config input output

compileObjectsJob config inputs output
  | isJust output = do
      hPutStrLn stderr "Cannot specify output file with multiple input files"
      return pass
  | otherwise = do
      -- Compile all input files independently
      jobs <- forM inputs $ \input -> compileObjectJob config input Nothing
      return $ sequence_ jobs

-- | Create a job to compile one input file to object code
compileObjectJob config (file_path, language) moutput_path = do
  input_language <- chooseLanguage (file_path, language)

  -- Read and compile the file.  Decide where to put the temporary C file.
  case input_language of
    TrioletLanguage -> do
      iface_files <- findInterfaceFiles True
      let infile = readFileFromPath file_path
          hfile = writeFileFromPath $ headerPath output_path
          hxxfile = writeFileFromPath $ hxxPath output_path
          ifile = writeFileFromPath $ ifacePath output_path
          outfile = writeFileFromPath output_path
      compileWithCFile config output_path $
        return $ \cfile -> pyonCompilation
                           (commandLineFlags config) infile iface_files
                           cfile ifile hfile hxxfile outfile

    LLTrioletLanguage ->
      let infile = readFileFromPath file_path
          ifile = writeFileFromPath $ ifacePath output_path
          outfile = writeFileFromPath output_path
      in compileWithCFile config output_path $
         return $ \cfile -> pyonAsmCompilation
                            (reverse $ ppMacros config)
                            (reverse $ includeSearchPaths config)
                            infile cfile ifile outfile
  where
    output_path =
      case moutput_path
      of Just p -> p
         Nothing -> replaceExtension file_path ".o"
         
-- Exported C function declarations go here
headerPath output_path = dropExtension output_path ++ "_interface.h"
    
-- Exported C++ function declarations go here
hxxPath output_path = dropExtension output_path ++ "_cxx.h"

-- Exported Pyon interface goes here
ifacePath output_path = replaceExtension output_path ".ti"

-- | Get all interface files
--
--   If @include_core@, then include the core module in the set of interface
--   files.  Otherwise don't.
findInterfaceFiles include_core = forM interface_files $ \fname -> do
  path <- getDataFileName ("interfaces" </> fname)
  return $ readFileFromPath path
  where
    -- These are the RTS interface files that were generated when
    -- the compiler was built
    interface_files =
      ["memory_py.ti", "prim.ti", "structures.ti", "list.ti",
       "inplace.ti", "buffer.ti", "lazy.ti"] ++ 
      if include_core then ["coremodule.ti"] else []
   
-- | Compile and generate an intermediate C file.
-- If C files are kept, put the C file in the same location as the output, with
-- a different extension.  Otherwise, make an anonymous file.
compileWithCFile config output_path mk_do_work
  | keepCFiles config = do
      temp_file <- tempFileFromPath True (output_path `replaceExtension` ".c")
      do_work <- mk_do_work
      return $ do_work temp_file
  | otherwise = do
      do_work <- mk_do_work
      return $ withAnonymousFile ".c" $ do_work

builtinLibraryCompilation :: CompileFlags -- ^ Command-line flags
                          -> [ReadFile]   -- ^ Input interface files
                          -> TempFile     -- ^ Temporary C file
                          -> WriteFile    -- ^ Output interface file
                          -> WriteFile    -- ^ Output object file
                          -> Job ()
builtinLibraryCompilation compile_flags iface_files cfile ifile outfile = do
  --high_level <- taskJob GetBuiltins
  --asm <- taskJob $ CompilePyonMemToPyonAsm compile_flags high_level
  asm <- taskJob CompileBuiltinsToPyonAsm
  ifaces <- mapM (taskJob . LoadIface) iface_files
  taskJob $ CompilePyonAsmToGenC asm ifaces (writeTempFile cfile) ifile writeNothing writeNothing
  taskJob $ CompileGenCToObject (readTempFile cfile) outfile

pyonCompilation :: CompileFlags -- ^ Command-line flags
                -> ReadFile     -- ^ Input pyon file
                -> [ReadFile]   -- ^ Input interface files
                -> TempFile     -- ^ Temporary C file
                -> WriteFile    -- ^ Output interface file
                -> WriteFile    -- ^ Output C header file
                -> WriteFile    -- ^ Output C++ header file
                -> WriteFile    -- ^ Output object file
                -> Job ()
pyonCompilation compile_flags infile iface_files cfile ifile hfile hxxfile outfile = do
  high_level <- taskJob $ ParsePyon compile_flags infile
  asm <- taskJob $ CompilePyonMemToPyonAsm compile_flags high_level
  ifaces <- mapM (taskJob . LoadIface) iface_files
  taskJob $ CompilePyonAsmToGenC asm ifaces (writeTempFile cfile) ifile hfile hxxfile
  taskJob $ CompileGenCToObject (readTempFile cfile) outfile

pyonAsmCompilation :: [(String, Maybe String)] -- ^ Preprocessor macros
                   -> [String]                 -- ^ Include paths
                   -> ReadFile  -- ^ Input llt file
                   -> TempFile  -- ^ Temporary C file
                   -> WriteFile -- ^ Output interface file
                   -> WriteFile -- ^ Output object file
                   -> Job ()
pyonAsmCompilation macros search_paths infile cfile ifile outfile = do
  asm <- withAnonymousFile ".llt" $ \ppfile -> do
    taskJob $ PreprocessCPP macros search_paths infile (writeTempFile ppfile)
    taskJob $ ParsePyonAsm (readTempFile ppfile)
    
  -- Don't link to any interfaces
  taskJob $ CompilePyonAsmToGenC asm [] (writeTempFile cfile) ifile writeNothing writeNothing
  taskJob $ CompileGenCToObject (readTempFile cfile) outfile

