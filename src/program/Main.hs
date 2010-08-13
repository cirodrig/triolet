
{-# LANGUAGE ForeignFunctionInterface #-}
module Main(main) where

import Control.Exception
import Control.Monad
import System.Cmd
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.IO
import Text.PrettyPrint.HughesPJ

import Gluon.Eval.Error
import InitializeGlobals
import CommandLine
import Job
import Paths_pyon
import Parser.Driver
import Untyped.InitializeBuiltins
import qualified Untyped.Print as Untyped
import qualified Untyped.TypeInference as Untyped
import qualified SystemF.PartialEval as SystemF
import qualified SystemF.DeadCode as SystemF
import qualified SystemF.ElimPatternMatching as SystemF
import qualified SystemF.StreamSpecialize as SystemF
import qualified SystemF.Typecheck as SystemF
import qualified SystemF.NewFlatten.GenCore as SystemF
import qualified SystemF.Print as SystemF
import qualified Core.Lowering as Core
import qualified Core.Print as Core
import qualified LowLevel.Syntax as LowLevel
import qualified LowLevel.Print as LowLevel
import qualified LowLevel.RecordFlattening as LowLevel
import qualified LowLevel.BuiltinCalls as LowLevel
import qualified LowLevel.Closures as LowLevel
import qualified LowLevel.ReferenceCounting as LowLevel
import qualified LowLevel.GenerateC as LowLevel
import qualified LLParser.Parser as LLParser

main = do
  -- Initialiation
  loadBuiltins
  initializeTIBuiltins
  
  -- Parse arguments
  job <- parseCommandLineArguments
  
  -- Do work
  runJob runTask job
  
-- | Run a task.  This is the entry point for each stage of the
-- compiler.
runTask :: Task a -> IO a
runTask (ReadInputFile path) = do
  return $ diskFile path

runTask (PreprocessCPP file) = do
  output_file <- newTemporaryFile ".out"
  input_path <- getFilePath file
  output_path <- getFilePath output_file
  invokeCPP input_path output_path
  return output_file

runTask (ParsePyonAsm file) = do
  input_text <- readDataFileString file
  input_path <- getFilePath file
  parsePyonAsm input_path input_text

runTask (CompilePyonToPyonAsm file) = do
  input_text <- readDataFileString file
  input_path <- getFilePath file
  compilePyonToPyonAsm input_path input_text

runTask (CompilePyonAsmToObject ll_mod) = do
  output_file <- newTemporaryFile ".o"
  compilePyonAsmToObject ll_mod output_file
  return output_file

runTask (RenameToPath path file) = do
  input_path <- getFilePath file
  renameFile input_path path

-- | Invoke the C preprocessor
invokeCPP :: FilePath -> FilePath -> IO ()
invokeCPP inpath outpath = do
  rc <- rawSystem "gcc" cpp_opts
  unless (rc == ExitSuccess) $ do
    putStrLn "Compilation failed: Error in C preprocessor" 
    exitFailure  
  where
    cpp_opts =
      [ "-E"                    -- preprocess only
      , "-xc"                   -- preprocess in C mode
      , "-nostdinc"             -- do not search standard include paths
      , inpath                  -- input path
      , "-o", outpath           -- output path
      ]

-- | Compile a pyon file from source code to low-level code.
compilePyonToPyonAsm :: FilePath -> String -> IO LowLevel.Module
compilePyonToPyonAsm path text = do
  -- Parse and generate untyped code
  untyped_mod <- parseFile path text
  putStrLn "Untyped"
  print $ Untyped.pprModule untyped_mod
  
  -- System F transformations
  sf_mod <- Untyped.typeInferModule untyped_mod
  sf_mod <- return $ SystemF.partialEvaluateModule sf_mod
  sf_mod <- return $ SystemF.eliminateDeadCode sf_mod
  sf_mod <- SystemF.eliminatePatternMatching sf_mod
  sf_mod <- SystemF.doSpecialization sf_mod
  putStrLn ""
  putStrLn "System F"
  print $ SystemF.pprModule sf_mod
  
  -- Convert to core
  flat_mod <- do
    tc_mod <- SystemF.typeCheckModule sf_mod
    case tc_mod of
      Left errs -> do mapM_ (putStrLn . showTypeCheckError) errs
                      fail "Type checking failed in core"
      Right m -> SystemF.flatten m

  putStrLn ""
  putStrLn "Core"
  print $ vcat $ map (vcat . map Core.pprCDef) flat_mod

  -- Convert to low-level form
  ll_mod <- Core.lower flat_mod
  putStrLn ""
  putStrLn "Lowered"
  print $ LowLevel.pprModule ll_mod
  
  return ll_mod

parsePyonAsm input_path input_text = do
  LLParser.parseFile input_path input_text
  print "Not implemented: Parsing Pyon ASM"
  return undefined

-- | Compile an input low-level module to object code
compilePyonAsmToObject ll_mod output_file = do
  -- Low-level transformations
  ll_mod <- LowLevel.flattenRecordTypes =<< LowLevel.makeBuiltinPrimOps ll_mod
  putStrLn ""
  putStrLn "Lowered and flattened"
  print $ LowLevel.pprModule ll_mod
  
  ll_mod <- LowLevel.closureConvert ll_mod
  putStrLn ""
  putStrLn "Closure converted"
  print $ LowLevel.pprModule ll_mod  

  ll_mod <- LowLevel.insertReferenceCounting ll_mod
  
  -- Generate and compile a C file
  let c_mod = LowLevel.generateCFile ll_mod
      
  c_file <- newTemporaryFile ".c"
  writeDataFileString c_file c_mod
    
  -- Compile the file
  compileCFile c_file output_file
  
  return ()

-- | Compile a C file to produce an object file.
compileCFile c_file o_file = do
  c_fname <- getFilePath c_file
  o_fname <- getFilePath o_file
  include_path <- Paths_pyon.getDataFileName "include"
  let compiler_opts =
        [ "-c"                  -- Compile
        , "-g"                  -- Emit debug information
        , "-m32"                -- 32-bit mode
        , "-xc"                 -- Source is a C file
        , c_fname               -- Input filename
        , "-o", o_fname         -- Output filename
        , "-I" ++ include_path  -- Include directory
        ]
  rc <- rawSystem "gcc" compiler_opts
  unless (rc == ExitSuccess) $ do
    putStrLn "Compilation failed: Error in C backend phase" 
    exitFailure
