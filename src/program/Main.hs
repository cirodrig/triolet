
{-# LANGUAGE ForeignFunctionInterface #-}
module Main(main) where

import Control.Exception
import Control.Monad
import Data.Binary
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
import Paths
import Parser.Driver
import Untyped.InitializeBuiltins
import qualified Untyped.Print as Untyped
import qualified Untyped.TypeInference as Untyped
import qualified SystemF.PartialEval as SystemF
import qualified SystemF.DeadCode as SystemF
import qualified SystemF.ElimPatternMatching as SystemF
import qualified SystemF.StreamSpecialize as SystemF
import qualified SystemF.Typecheck as SystemF
import qualified SystemF.Flatten.EffectInference as SystemF
import qualified SystemF.Print as SystemF
import qualified Core.Lowering as Core
import qualified Core.Print as Core
import qualified Core.PartialEval as Core
import qualified Core.Unpacking as Core
import qualified Core.Rewriting as Core
import qualified LowLevel.Syntax as LowLevel
import qualified LowLevel.Print as LowLevel
import qualified LowLevel.RecordFlattening as LowLevel
import qualified LowLevel.BuiltinCalls as LowLevel
import qualified LowLevel.CSE as LowLevel
import qualified LowLevel.Closures as LowLevel
import qualified LowLevel.DeadCode as LowLevel
import qualified LowLevel.ReferenceCounting as LowLevel
import qualified LowLevel.GenerateC as LowLevel
import qualified LowLevel.GenerateCHeader as LowLevel
import qualified LowLevel.Inlining as LowLevel
import qualified LowLevel.InterfaceFile as LowLevel
import qualified LLParser.Parser as LLParser
import qualified LLParser.TypeInference as LLParser
import qualified LLParser.GenLowLevel2 as LLParser

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
runTask (PreprocessCPP { cppInput = in_file
                       , cppOutput = cpp_file}) = do
  in_path <- readFilePath in_file
  out_path <- writeFilePath cpp_file
  invokeCPP in_path out_path

runTask (ParsePyonAsm {parseAsmInput = file}) = do
  input_text <- readFileAsString file
  input_path <- readFilePath file
  parsePyonAsm input_path input_text

runTask (CompilePyonToPyonAsm {compilePyonInput = file}) = do
  input_text <- readFileAsString file
  input_path <- readFilePath file
  compilePyonToPyonAsm input_path input_text

runTask (CompilePyonAsmToGenC { compileAsmInput = ll_mod
                              , compileAsmIfaces = ifaces
                              , compileAsmOutput = c_file
                              , compileAsmInterface = i_file
                              , compileAsmHeader = h_file}) = do
  compilePyonAsmToGenC ll_mod ifaces c_file i_file h_file

runTask (LoadIface {loadIfaceInput = iface_file}) = do
  loadIface iface_file

runTask (CompileGenCToObject { compileGenCInput = c_file
                             , compileGenCOutput = o_file}) = do
  c_path <- readFilePath c_file 
  o_path <- writeFilePath o_file
  compileCFile c_path o_path

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
  
  -- Generate System F
  sf_mod <- Untyped.typeInferModule untyped_mod
  
  -- System F transformations
  sf_mod <- return $ SystemF.partialEvaluateModule sf_mod
  sf_mod <- return $ SystemF.eliminateDeadCode sf_mod
  sf_mod <- SystemF.eliminatePatternMatching sf_mod
  sf_mod <- SystemF.doSpecialization sf_mod

  -- Re-run partial evaluation to simplify the specialized code.
  -- In particular, we must put 'do' operators into standard form.
  sf_mod <- return $ SystemF.partialEvaluateModule sf_mod
  putStrLn ""
  putStrLn "System F"
  print $ SystemF.pprModule sf_mod
  
  -- Convert to core
  flat_mod <- do
    tc_mod <- SystemF.typeCheckModule sf_mod
    case tc_mod of
      Left errs -> do mapM_ (putStrLn . showTypeCheckError) errs
                      fail "Type checking failed in core"
      Right m -> do SystemF.inferSideEffects m
                    -- SystemF.flatten m

  putStrLn ""
  putStrLn "Core"
  print $ Core.pprCModule flat_mod

  -- Simplify core
  flat_mod <- return $ Core.partialEvaluate flat_mod
  flat_mod <- Core.unpackDataStructures flat_mod
  flat_mod <- Core.rewrite flat_mod
  flat_mod <- return $ Core.partialEvaluate flat_mod

  putStrLn ""
  putStrLn "Simplified core"
  print $ Core.pprCModule flat_mod

  -- Convert to low-level form
  ll_mod <- Core.lower flat_mod
  putStrLn ""
  putStrLn "Lowered"
  print $ LowLevel.pprModule ll_mod
  
  return ll_mod

parsePyonAsm input_path input_text = do
  (mod_name, externs, ast) <- LLParser.parseFile input_path input_text
  (t_externs, t_defs) <-
    LLParser.typeInferModule input_path mod_name externs ast
  LLParser.generateLowLevelModule mod_name t_externs t_defs

loadIface iface_file = do
  bs <- readFileAsByteString iface_file
  return $ decode bs

-- | Compile an input low-level module to C code.  Generate an interface file.
-- Generate a header file if there are exported routines.
compilePyonAsmToGenC ll_mod ifaces c_file i_file h_file = do
  -- Low-level transformations
  ll_mod <- LowLevel.makeBuiltinPrimOps ll_mod
  ll_mod <- LowLevel.flattenRecordTypes ll_mod
  putStrLn ""
  putStrLn "Lowered and flattened"
  print $ LowLevel.pprModule ll_mod
  
  -- Link to interfaces
  ll_mod <- foldM (flip LowLevel.addInterfaceToModuleImports) ll_mod ifaces
  
  -- First round of optimizations
  ll_mod <- LowLevel.commonSubexpressionElimination ll_mod
  ll_mod <- return $ LowLevel.eliminateDeadCode ll_mod
  ll_mod <- LowLevel.inlineModule ll_mod
  ll_mod <- LowLevel.commonSubexpressionElimination ll_mod
  ll_mod <- return $ LowLevel.eliminateDeadCode ll_mod
  putStrLn ""
  putStrLn "Optimized"
  print $ LowLevel.pprModule ll_mod  
  
  -- Generate interface file
  (ll_mod, ll_interface) <- LowLevel.createModuleInterface ll_mod
  writeFileAsByteString i_file $ encode ll_interface

  -- Closure converion
  ll_mod <- LowLevel.closureConvert ll_mod
  putStrLn ""
  putStrLn "Closure converted"
  print $ LowLevel.pprModule ll_mod  

  ll_mod <- LowLevel.insertReferenceCounting ll_mod
  putStrLn ""
  putStrLn "Reference counting"
  print $ LowLevel.pprModule ll_mod  
  
  -- Generate and compile a C file
  c_mod <- LowLevel.generateCFile ll_mod
      
  writeFileAsString c_file c_mod
  
  when (LowLevel.moduleHasExports ll_mod) $
    let h_mod = LowLevel.generateCHeader ll_mod
    in writeFileAsString h_file h_mod

-- | Compile a C file to produce an object file.
compileCFile c_fname o_fname = do
  include_path <- Paths.getDataFileName "include"
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
