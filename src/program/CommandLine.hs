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

-- | A command-line option modifies the option interpreter state
newtype Opt = Opt (InterpretOptsState -> InterpretOptsState)

instance Monoid Opt where
  mempty = Opt id
  Opt f `mappend` Opt g = Opt (g . f)

optionDescrs =
  [ Option "h" ["help"] (NoArg (Opt $ setAction GetHelp))
    "display usage information"
  , Option "" ["keep-c-files"] (NoArg (Opt setKeepCFiles)) 
    "save generated C files in output directory"
  , Option "x" [] (ReqArg (\lang -> Opt $ setLanguage lang) "LANG")
    ("specify input language\n" ++
     "(options are 'none', 'pyon', 'pyonasm')")
  , Option "o" [] (ReqArg (\file -> Opt $ setOutput file) "FILE")
    "specify output file"
  , Option "D" [] (ReqArg (\mac -> Opt $ addMacro mac) "MACRO")
    "define a preprocessor macro; ignored when compiling pyon files"
  , Option "I" [] (ReqArg (\mac -> Opt $ addIncludePath mac) "PATH")
    "add a path to the include search path; ignored when compiling pyon files"
  , Option "f" [] (ReqArg (Opt . addFlag) "FLAG")
    "enable/disable a compiler flag"
  ]

-- | Parse command-line arguments.  If they specify a job to perform, return
-- the job.
parseCommandLineArguments :: IO (Job ())
parseCommandLineArguments = do
  raw_args <- getArgs
  let args = snd $ splitDataFilePath raw_args
  let (options, _, errors) =
        getOpt (ReturnInOrder (\file -> Opt $ addFile file)) optionDescrs args

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
  let commands = case mconcat opts of Opt f -> f initialState
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
               in compileObjectsJob commands inputs output
             ConflictingAction -> do
               hPutStrLn stderr "Conflicting commands given on command line"
               hPutStrLn stderr "For usage information, invoke with --help"
               return pass

data InterpretOptsState =
  InterpretOptsState
  { currentAction :: !Action 
  , currentLanguage :: !Language
  , outputFile :: Maybe String
    -- | Do we save temporary C files?
  , keepCFiles :: {-# UNPACK #-} !Bool
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
  }

initialState = InterpretOptsState { currentAction = CompileObject
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
               , ("pyon", PyonLanguage)
               , ("pyonasm", PyonAsmLanguage)
               ]

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
  in st {inputFiles = (file, lang) : inputFiles st}

-------------------------------------------------------------------------------
-- Job creation

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
  input_language <-
    case language
    of NoneLanguage -> from_suffix file_path
       _ -> return language

  -- Read and compile the file.  Decide where to put the temporary C file.
  case input_language of
    PyonLanguage -> do
      iface_files <- find_interface_files
      let infile = readFileFromPath file_path
          hfile = writeFileFromPath header_path
          ifile = writeFileFromPath iface_path
          outfile = writeFileFromPath output_path
      compileWithCFile config output_path $
        return $ \cfile -> pyonCompilation
                           (commandLineFlags config) infile iface_files
                           cfile ifile hfile outfile

    PyonAsmLanguage ->
      let infile = readFileFromPath file_path
          ifile = writeFileFromPath iface_path
          outfile = writeFileFromPath output_path
      in compileWithCFile config output_path $
         return $ \cfile -> pyonAsmCompilation
                            (reverse $ ppMacros config)
                            (reverse $ includeSearchPaths config)
                            infile cfile ifile outfile
  where
    from_suffix path
      | takeExtension path == ".pyon" = return PyonLanguage
      | takeExtension path == ".pyasm" = return PyonAsmLanguage
      | otherwise = let msg = "Cannot determine language of '" ++ path ++ "'"
                    in fail msg
    
    -- Exported C function declarations go here
    header_path = dropExtension output_path ++ "_interface.h"
    
    -- Exported Pyon interface goes here
    iface_path = replaceExtension output_path ".pi"

    output_path =
      case moutput_path
      of Just p -> p
         Nothing -> replaceExtension file_path ".o"
         
    -- Get all interface files
    find_interface_files = forM interface_files $ \fname -> do
      path <- getDataFileName ("interfaces" </> fname)
      return $ readFileFromPath path
      where
        -- These are the RTS interface files that were generated when
        -- the compiler was built
        interface_files =
          ["memory_py.pi", "prim.pi", "structures.pi", "list.pi", "stream.pi",
           "effects.pi"]
   
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

pyonCompilation :: CompileFlags -- ^ Command-line flags
                -> ReadFile     -- ^ Input pyon file
                -> [ReadFile]   -- ^ Input interface files
                -> TempFile     -- ^ Temporary C file
                -> WriteFile    -- ^ Output interface file
                -> WriteFile    -- ^ Output header file
                -> WriteFile    -- ^ Output object file
                -> Job ()
pyonCompilation compile_flags infile iface_files cfile ifile hfile outfile = do
  asm <- taskJob $ CompilePyonToPyonAsm compile_flags infile
  ifaces <- mapM (taskJob . LoadIface) iface_files
  taskJob $ CompilePyonAsmToGenC asm ifaces (writeTempFile cfile) ifile hfile
  taskJob $ CompileGenCToObject (readTempFile cfile) outfile

pyonAsmCompilation :: [(String, Maybe String)] -- ^ Preprocessor macros
                   -> [String]                 -- ^ Include paths
                   -> ReadFile  -- ^ Input pyasm file
                   -> TempFile  -- ^ Temporary C file
                   -> WriteFile -- ^ Output interface file
                   -> WriteFile -- ^ Output object file
                   -> Job ()
pyonAsmCompilation macros search_paths infile cfile ifile outfile = do
  asm <- withAnonymousFile ".pyasm" $ \ppfile -> do
    taskJob $ PreprocessCPP macros search_paths infile (writeTempFile ppfile)
    taskJob $ ParsePyonAsm (readTempFile ppfile)
    
  -- Don't link to any interfaces
  taskJob $ CompilePyonAsmToGenC asm [] (writeTempFile cfile) ifile writeNothing
  taskJob $ CompileGenCToObject (readTempFile cfile) outfile

