{-| Command line parsing.

The exported function, 'parseCommandLineArguments', interprets the program's 
command line.  If the command line is ill-formed, or the given command is to
print a help message, it will print messages and end the program.  Otherwise
it will return a 'Job' describing the actions to perform.

The command line is first parsed into individual options with 'getOpt'.  Then
the options are processed one at a time, and the result is turned into a 'Job'.
-}

module CommandLine(parseCommandLineArguments)
where

import Control.Monad
import Control.Monad.State
import Data.Maybe
import System.Console.GetOpt
import System.Environment
import System.FilePath
import System.IO

import Job

-- | An action to be taken 
data Action =
    GetUsage                    -- ^ Show a usage string
  | GetHelp                     -- ^ Get help documentation
  | CompileObject               -- ^ Compile to object code
  | ConflictingAction           -- ^ Conflicting options given
    deriving(Eq)

-- | Priority of an action.  Higher-priority actions override lower-priority
-- actions.
actionPriority :: Action -> Int
actionPriority GetUsage = 0
actionPriority GetHelp = 10
actionPriority CompileObject = 1
actionPriority ConflictingAction = 11

-- | A language to process
data Language =
    NoneLanguage                -- ^ Infer language based on file extension
  | PyonLanguage                -- ^ Pyon code
  | PyonAsmLanguage             -- ^ Low-level Pyon code

-- | A command-line option
data Opt =
    ActionOpt !Action           -- ^ Action to perform
  | LanguageOpt !String         -- ^ Language to use
  | OutputOpt !String           -- ^ Output file
  | PositionalOpt !String       -- ^ Input file (positional argument)

optionDescrs =
  [ Option "h" ["help"] (NoArg (ActionOpt GetHelp))
    "display usage information"
  , Option "x" [] (ReqArg LanguageOpt "LANG")
    ("specify input language\n" ++
     "(options are 'none', 'pyon', 'pyonasm')")
  , Option "o" [] (ReqArg OutputOpt "FILE")
    "specify output file"
  ]

-- | Parse command-line arguments.  If they specify a job to perform, return
-- the job.
parseCommandLineArguments :: IO (Job ())
parseCommandLineArguments = do
  args <- getArgs
  let (options, _, errors) =
        getOpt (ReturnInOrder PositionalOpt) optionDescrs args

  -- Print errors or create a job
  if not $ null errors
    then do mapM_ putStrLn errors
            return pass
    else interpretOptions options

usageHeader = do
  program <- getProgName
  let usage = "Usage: " ++ program ++ " [OPTION...] files..."
  return usage

-------------------------------------------------------------------------------
-- Interpret command-line options

interpretOptions :: [Opt] -> IO (Job ())
interpretOptions opts =
  let commands = execState (mapM_ interpret opts) initialState
  in case reverse $ interpreterErrors commands
     of xs@(_:_) -> do mapM_ (hPutStrLn stderr) xs
                       return pass
        [] ->
          case currentAction commands
          of GetUsage -> do
               -- Print brief usage info and exit
               header <- usageHeader
               putStrLn header
               putStrLn "For usage information, invoke with --help"
               return pass
             GetHelp -> do
               -- Print usage info and exist
               header <- usageHeader
               putStrLn $ usageInfo header optionDescrs
               return pass
             CompileObject ->
               let inputs = reverse $ inputFiles commands
                   output = outputFile commands
               in compileObjectsJob inputs output
             ConflictingAction -> do
               hPutStrLn stderr "Conflicting commands given on command line"
               hPutStrLn stderr "For usage information, invoke with --help"
               return pass
  where
    interpret (ActionOpt act)      = setAction act
    interpret (LanguageOpt lang)   = setLanguage lang
    interpret (OutputOpt file)     = setOutput file
    interpret (PositionalOpt file) = addFile file

data InterpretOptsState =
  InterpretOptsState
  { currentAction :: !Action 
  , currentLanguage :: !Language
  , outputFile :: Maybe String
    -- | List of input files and languages, in /reverse/ order
  , inputFiles :: [(String, Language)]
    -- | List of error messages, in /reverse/ order
  , interpreterErrors :: [String]
  }

initialState = InterpretOptsState { currentAction = CompileObject
                                  , currentLanguage = NoneLanguage
                                  , outputFile = Nothing
                                  , inputFiles = []
                                  , interpreterErrors = []
                                  }

putError e = modify $ \s -> s {interpreterErrors = e : interpreterErrors s}

setAction new = do
  old <- gets currentAction
  case actionPriority old `compare` actionPriority new of
    GT -> update_action old
    LT -> update_action new
    EQ | old == new -> update_action new
       | otherwise  -> update_action ConflictingAction
  where
    update_action a = modify $ \s -> s {currentAction = a}

setLanguage lang_string =
  case language
  of Just l  -> modify $ \s -> s {currentLanguage = l}
     Nothing -> putError $ "Unrecognized language: " ++ lang_string
  where
    language = lookup lang_string
               [ ("none", NoneLanguage)
               , ("pyon", PyonLanguage)
               , ("pyonasm", PyonAsmLanguage)
               ]

setOutput file = do
  old_file <- gets outputFile
  case old_file of
    Nothing -> modify $ \s -> s {outputFile = Just file}
    Just _  -> putError $ "Only one output file may be given"

addFile file = do
  lang <- gets currentLanguage
  modify $ \s -> s {inputFiles = (file, lang) : inputFiles s}

-------------------------------------------------------------------------------
-- Job creation

-- | Create a job to compile one input file to object code
compileObjectJob (file_path, language) moutput_path = do
  input_language <-
    case language
    of NoneLanguage -> from_suffix file_path
       _ -> return language

  -- Read and compile the file
  case input_language of
    PyonLanguage -> return $ pyonCompilation file_path >>=
                             fileOutput output_path
    PyonAsmLanguage -> return $ pyonAsmCompilation file_path >>=
                                fileOutput output_path
  where
    from_suffix path
      | takeExtension path == ".pyon" = return PyonLanguage
      | takeExtension path == ".pyasm" = return PyonAsmLanguage
      | otherwise = let msg = "Cannot determine language of '" ++ path ++ "'"
                    in fail msg
    
    output_path =
      case moutput_path
      of Just p -> p
         Nothing -> replaceExtension file_path ".o"

-- | Compile one or many object files
compileObjectsJob [] output = do
  hPutStrLn stderr "No input files" 
  return pass

compileObjectsJob [input] output =
  -- Allow overriding the output file name when one input file is given
  compileObjectJob input output

compileObjectsJob inputs output
  | isJust output = do
      hPutStrLn stderr "Cannot specify output file with multiple input files"
      return pass
  | otherwise = do
      -- Compile all input files independently
      jobs <- forM inputs $ \input -> compileObjectJob input Nothing
      return $ sequence_ jobs


pyonCompilation in_path = do
  input <- taskJob $ ReadInputFile in_path
  asm <- taskJob $ CompilePyonToPyonAsm input
  taskJob $ CompilePyonAsmToObject asm

pyonAsmCompilation in_path = do
  input <- taskJob $ ReadInputFile in_path
  ppinput <- taskJob $ PreprocessCPP input
  asm <- taskJob $ ParsePyonAsm ppinput
  taskJob $ CompilePyonAsmToObject asm

fileOutput out_path file = taskJob $ RenameToPath out_path file
