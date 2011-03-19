
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

import InitializeGlobals
import CommandLine
import Job
import Paths
import Parser.Driver
import Untyped.InitializeBuiltins
import qualified Untyped.Print as Untyped
import qualified Untyped.TypeInference as Untyped
import qualified SystemF.ArgumentFlattening as SystemF
import qualified SystemF.PartialEval as SystemF
import qualified SystemF.DeadCodeSF
import qualified SystemF.DemandAnalysis as SystemF
import qualified SystemF.ElimPatternMatching as SystemF
import qualified SystemF.StreamSpecialize as SystemF
import qualified SystemF.TypecheckSF
import qualified SystemF.TypecheckMem
import qualified SystemF.Simplify as SystemF
import qualified SystemF.Lowering.Lowering2 as SystemF
import qualified SystemF.Print as SystemF
import qualified SystemF.PrintMemoryIR
import qualified SystemF.OutputPassing as SystemF
import qualified SystemF.Floating as SystemF
import qualified LowLevel.Syntax as LowLevel
import qualified LowLevel.Print as LowLevel
import qualified LowLevel.RecordFlattening as LowLevel
import qualified LowLevel.CSE as LowLevel
import qualified LowLevel.Closures as LowLevel
import qualified LowLevel.DeadCode as LowLevel
import qualified LowLevel.LambdaConvert as LowLevel
import qualified LowLevel.LocalCPS as LowLevel
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
  
iterateM :: Monad m => (a -> m a) -> Int -> a -> m a
iterateM f n x = go n x 
  where
    go 0 x = return x
    go n x = f x >>= go (n-1)

-- | Run a task.  This is the entry point for each stage of the
-- compiler.
runTask :: Task a -> IO a
runTask (PreprocessCPP { cppMacros = macros
                       , cppIncludeSearchPaths = include_paths
                       , cppInput = in_file
                       , cppOutput = cpp_file}) = do
  in_path <- readFilePath in_file
  out_path <- writeFilePath cpp_file
  invokeCPP macros include_paths in_path out_path

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
invokeCPP :: [(String, Maybe String)] -> [FilePath] -> FilePath -> FilePath -> IO ()
invokeCPP macros include_paths inpath outpath = do
  rc <- rawSystem "gcc" cpp_opts
  unless (rc == ExitSuccess) $ do
    putStrLn "Compilation failed: Error in C preprocessor" 
    exitFailure  
  where
    cpp_opts =
      macro_opts ++
      include_path_opts ++
      [ "-E"                    -- preprocess only
      , "-xc"                   -- preprocess in C mode
      , "-nostdinc"             -- do not search standard include paths
      , inpath                  -- input path
      , "-o", outpath           -- output path
      ]
    macro_opts = [ "-D" ++ key ++ maybe "" ('=':) value
                 | (key, value) <- macros]
    include_path_opts = ["-I" ++ path | path <- include_paths]

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
  sf_mod <- SystemF.DeadCodeSF.eliminateDeadCode sf_mod
  sf_mod <- SystemF.eliminatePatternMatching sf_mod
  -- sf_mod <- SystemF.doSpecialization sf_mod

  -- Re-run partial evaluation to simplify the specialized code.
  -- In particular, we must put 'do' operators into standard form.
  sf_mod <- return $ SystemF.partialEvaluateModule sf_mod
  putStrLn ""
  putStrLn "System F"
  print $ SystemF.pprModule sf_mod
  
  -- Convert to explicit memory representation
  tc_mod <- SystemF.TypecheckSF.typeCheckModule sf_mod
  mem_mod <- SystemF.generateMemoryIR tc_mod
    
  putStrLn "Memory"
  print $ SystemF.PrintMemoryIR.pprModule mem_mod
  
  -- Optimizations on memory representation.
  -- The first group of optimizations performs inlining to create bigger 
  -- functions, then floating and dead code elimination.  These steps 
  -- are primarily setup to improve the accuracy of the simplifier.
  mem_mod <- SystemF.rewriteLocalExpr mem_mod
  mem_mod <- SystemF.floatModule mem_mod
  mem_mod <- SystemF.demandAnalysis mem_mod

  putStrLn "Prepared Memory"
  print $ SystemF.PrintMemoryIR.pprModule mem_mod

  -- The next group of optimizations does the main set of optimizations,
  -- including high-level transformations via rewriting.
  -- Currently there are inter-pass dependences that we
  -- stupidly resolve by running them lots of times.
  mem_mod <- SystemF.rewriteLocalExpr mem_mod
  mem_mod <- SystemF.floatModule mem_mod
  mem_mod <- SystemF.demandAnalysis mem_mod
  mem_mod <- iterateM (SystemF.rewriteLocalExpr >=>
                       SystemF.floatModule >=>
                       SystemF.localDemandAnalysis) 7 mem_mod
  mem_mod <- SystemF.rewriteLocalExpr mem_mod
  mem_mod <- SystemF.floatModule mem_mod
  mem_mod <- SystemF.demandAnalysis mem_mod

  -- Flatten function arguments and local variables.
  -- We transform arguments and returns first, then run a simplifier pass 
  -- to rebuild demand information.
  -- Argument flattening leads to more precise demand information,
  -- which makes local variable flattening more effective.
  mem_mod <- SystemF.flattenArguments mem_mod
  mem_mod <- SystemF.rewriteLocalExpr mem_mod
  mem_mod <- SystemF.floatModule mem_mod
  mem_mod <- SystemF.demandAnalysis mem_mod
  mem_mod <- SystemF.flattenLocals mem_mod
  
  -- Re-run the simplifier to eliminate redundant code left behind by
  -- flattening
  mem_mod <- iterateM (SystemF.rewriteLocalExpr >=>
                       SystemF.floatModule >=>
                       SystemF.localDemandAnalysis) 4 mem_mod

  putStrLn "Optimized Memory"
  print $ SystemF.PrintMemoryIR.pprModule mem_mod

  -- Lower
  tc_mem_mod <- SystemF.TypecheckMem.typeCheckModule mem_mod
  --SystemF.inferSideEffects tc_mod
  ll_mod <- SystemF.lowerModule tc_mem_mod

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
  print $ LowLevel.pprModule ll_mod
  -- Low-level transformations
  ll_mod <- LowLevel.flattenRecordTypes ll_mod
  
  -- Link to interfaces
  ll_mod <- foldM (flip LowLevel.addInterfaceToModuleImports) ll_mod ifaces
  putStrLn ""
  putStrLn "Lowered and flattened"
  print $ LowLevel.pprModule ll_mod
  
  -- First round of optimizations: Simplify code, and 
  -- eliminate trivial lambda abstractions that were introduced by lowering
  ll_mod <- LowLevel.commonSubexpressionElimination ll_mod
  ll_mod <- return $ LowLevel.eliminateDeadCode ll_mod
  ll_mod <- LowLevel.inlineModule ll_mod
  
  -- Second round of optimization: in addition to the other steps,
  -- convert lambdas to local functions.  This increases freedom for
  -- optimizing partial applications whose arguments are functions.
  ll_mod <- LowLevel.commonSubexpressionElimination ll_mod
  ll_mod <- LowLevel.lambdaConvert ll_mod
  ll_mod <- return $ LowLevel.eliminateDeadCode ll_mod
  ll_mod <- LowLevel.inlineModule ll_mod
  
-- Additional rounds: more inlining
  ll_mod <- iterateM (LowLevel.commonSubexpressionElimination >=>
                      return . LowLevel.eliminateDeadCode >=>
                      LowLevel.inlineModule) 3 ll_mod

  ll_mod <- LowLevel.commonSubexpressionElimination ll_mod
  ll_mod <- return $ LowLevel.eliminateDeadCode ll_mod
  ll_mod <- LowLevel.inlineModule ll_mod

  -- Cleanup
  ll_mod <- LowLevel.commonSubexpressionElimination ll_mod
  ll_mod <- return $ LowLevel.eliminateDeadCode ll_mod
  ll_mod <- return $ LowLevel.clearImportedFunctionDefinitions ll_mod
  putStrLn ""
  putStrLn "Optimized"
  print $ LowLevel.pprModule ll_mod  
  
  -- Generate interface file
  (ll_mod, ll_interface) <- LowLevel.createModuleInterface ll_mod
  writeFileAsByteString i_file $ encode ll_interface

  -- Closure conversion
  -- Remove any lambda values created by the last round of optimization
  ll_mod <- LowLevel.lambdaConvert ll_mod
  ll_mod <- LowLevel.lcpsModule ll_mod
  ll_mod <- return $ LowLevel.eliminateDeadCode ll_mod -- Minimize recursion groups
  ll_mod <- LowLevel.closureConvert ll_mod
  ll_mod <- LowLevel.insertReferenceCounting ll_mod
  
  -- Second round of optimizations
  ll_mod <- LowLevel.commonSubexpressionElimination ll_mod
  ll_mod <- return $ LowLevel.eliminateDeadCode ll_mod
  putStrLn ""
  putStrLn "Second optimization pass"
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
        , "-fPIC"               -- Position-independent code
        , "-xc"                 -- Source is a C file
        , c_fname               -- Input filename
        , "-o", o_fname         -- Output filename
        , "-I" ++ include_path  -- Include directory
        ]
  rc <- rawSystem "gcc" compiler_opts
  unless (rc == ExitSuccess) $ do
    putStrLn "Compilation failed: Error in C backend phase" 
    exitFailure
