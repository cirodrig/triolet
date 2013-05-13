{-# LANGUAGE ForeignFunctionInterface #-}
module Main(main) where

import Control.Exception
import Control.Monad
import Data.Binary
import System.Cmd
import System.CPUTime
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
import qualified Untyped.Print as Untyped
import qualified Untyped.Syntax as Untyped
import qualified Untyped.TypeInference2 as Untyped
import qualified SystemF.ArgumentFlattening as SystemF
-- import qualified SystemF.ConSpecialization as SystemF
import qualified SystemF.PartialEval as SystemF
import qualified SystemF.DeadCodeSF
import qualified SystemF.DemandAnalysis as SystemF
import qualified SystemF.Syntax as SystemF
import qualified SystemF.MemoryIR as SystemF
import qualified SystemF.TypecheckSF
import qualified SystemF.TypecheckMem
import qualified SystemF.Print as SystemF
import qualified SystemF.PrintMemoryIR
import qualified SystemF.Rename as SystemF
import qualified SystemF.ReprInference as SystemF
import qualified SystemF.Floating2 as SystemF
import qualified SystemF.Simplifier.Rewrite as SystemF
import qualified SystemF.Simplifier.Simplify as SystemF
import qualified SystemF.LoopRewrite as SystemF
import qualified SystemF.Lowering.Lowering2 as SystemF
import qualified LowLevel.Syntax as LowLevel
import qualified LowLevel.Print as LowLevel
import qualified LowLevel.RecordFlattening as LowLevel
import qualified LowLevel.RemoveUnits as LowLevel
import qualified LowLevel.CSE as LowLevel
import qualified LowLevel.Closures as LowLevel
import qualified LowLevel.DeadCode as LowLevel
import qualified LowLevel.ReferenceTracking as LowLevel
import qualified LowLevel.GenerateC as LowLevel
import qualified LowLevel.GenerateCHeader as LowLevel
import qualified LowLevel.GenerateCXXHeader as LowLevel
import qualified LowLevel.Inlining2
import qualified LowLevel.Lint as LowLevel
import qualified LowLevel.JoinPoints as LowLevel
import qualified LowLevel.InterfaceFile as LowLevel
import qualified LowLevel.NormalizeTail as LowLevel
import qualified LowLevel.Cxx.Wrappers
import qualified LLParser.Parser as LLParser
import qualified LLParser.TypeInference as LLParser
import qualified LLParser.GenLowLevel2 as LLParser
import qualified Globals
import GlobalVar
import Timer

debugMode = False

pprMemModule =
  SystemF.PrintMemoryIR.pprModuleFlags SystemF.PrintMemoryIR.tersePprFlags

main = do
  -- Parse arguments
  (global_values, job) <- parseCommandLineArguments

  -- Initialiation
  t1 <- getCPUTime
  loadBuiltins global_values
  t2 <- getCPUTime
  print "Initialization time"
  print (fromIntegral (t2 - t1) * 1e-12)
  
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

runTask (ParsePyon { parsePyonInput = file
                   , parseFlags = cflags}) = do
  input_text <- readFileAsString file
  input_path <- readFilePath file
  compilePyonToPyonMem cflags input_path input_text

runTask GetBuiltins = do
  -- Read the core module.
  -- The module was loaded during initialization.
  readInitGlobalVarIO Globals.the_coreModule

runTask (CompilePyonMemToPyonAsm { compileMemInput = mod
                                 , compileFlags = cflags}) = do
  compilePyonMemToPyonAsm cflags mod

runTask (CompilePyonAsmToGenC { compileAsmInput = ll_mod
                              , compileAsmIfaces = ifaces
                              , compileAsmOutput = c_file
                              , compileAsmInterface = i_file
                              , compileAsmHeader = h_file
                              , compileAsmCxxHeader = hxx_file}) = do
  compilePyonAsmToGenC ll_mod ifaces c_file i_file h_file hxx_file

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

-- | General-purpose high-level optimizations
highLevelOptimizations :: Times
                       -> Bool
                       -> SystemF.SimplifierPhase
                       -> SystemF.Module SystemF.Mem
                       -> IO (SystemF.Module SystemF.Mem)
highLevelOptimizations times global_demand_analysis simplifier_phase mod = do
  -- Run the rewriter (most optimizations are in here)
  mod <- time times RewriteTimer $
         SystemF.rewriteAtPhase simplifier_phase mod

  -- Specialize on constructors
  --mod <- time times SpecializeTimer $
  --       SystemF.specializeOnConstructors mod

  -- Demand information was destroyed by the previous passes.
  -- Re-run demand analysis.
  mod <- time times DemandTimer $
         if global_demand_analysis
         then SystemF.demandAnalysis mod
         else SystemF.localDemandAnalysis mod
  
  when debugMode $ void $ do    
    putStrLn "After rewrite"
    time times PrintTimer $ print $ pprMemModule mod
    time times TypecheckTimer $ evaluate $ SystemF.checkForShadowingModule mod -- DEBUG
    time times TypecheckTimer $ SystemF.TypecheckMem.typeCheckModule mod

  return mod

-- | Compile a pyon file from source code to high-level, unoptimized code.
compilePyonToPyonMem :: CompileFlags -> FilePath -> String
                     -> IO (SystemF.Module SystemF.Mem)
compilePyonToPyonMem compile_flags path text = do
  -- Parse and generate untyped code
  untyped_mod <- parseFile path text
  when debugMode $ void $ do
    putStrLn "Untyped"
    print $ Untyped.pprModule untyped_mod
  
  -- Generate System F
  sf_mod <- Untyped.typeInferModule untyped_mod
  
  when debugMode $ void $ do
    putStrLn ""
    putStrLn "System F"
    print $ SystemF.pprModule sf_mod

  -- _ <- SystemF.TypecheckSF.typeCheckModule sf_mod

  -- Convert to explicit memory representation  
  repr_mod <- SystemF.insertCoercions sf_mod

  -- Add predefined functions to the module
  repr_mod <- SystemF.insertGlobalSystemFFunctions repr_mod

  when debugMode $ void $ do
    putStrLn ""
    putStrLn "Memory IR"
    print $ pprMemModule repr_mod

    -- Check for type errors produced by previous steps
    SystemF.TypecheckMem.typeCheckModule repr_mod
  
  return repr_mod

compilePyonMemToPyonAsm :: CompileFlags -> SystemF.Module SystemF.Mem
                        -> IO LowLevel.Module
compilePyonMemToPyonAsm compile_flags repr_mod = do

  times <- newTimes
  
  -- DEBUG: Run demand analysis
  repr_mod <- SystemF.demandAnalysis repr_mod
  putStrLn "After demand analysis"
  print $ pprMemModule repr_mod

  -- General-purpose, high-level optimizations
  repr_mod <- highLevelOptimizations times True SystemF.GeneralSimplifierPhase repr_mod

  repr_mod <- time times FloatingTimer $ SystemF.longRangeFloating repr_mod
  time times PrintTimer $ when debugMode $ void $ do
    putStrLn "After floating 1"
    print $ pprMemModule repr_mod
    evaluate $ SystemF.checkForShadowingModule repr_mod

  repr_mod <- highLevelOptimizations times True SystemF.GeneralSimplifierPhase repr_mod
  repr_mod <- iterateM (highLevelOptimizations times False SystemF.GeneralSimplifierPhase) 5 repr_mod
  
  time times PrintTimer $ when debugMode $ void $ do
    putStrLn ""
    putStrLn "Before loop dimension analysis"
    print $ pprMemModule repr_mod

  repr_mod <- iterateM (highLevelOptimizations times True SystemF.DimensionalitySimplifierPhase) 7 repr_mod

  time times PrintTimer $ when debugMode $ void $ do
    putStrLn ""
    putStrLn "Before parallelizing"
    print $ pprMemModule repr_mod

  -- Parallelize outer loops
  repr_mod <-
    if lookupCompileFlag DoParallelization compile_flags
    then do repr_mod <- time times ParallelizeTimer $ SystemF.parallelLoopRewrite repr_mod
            time times PrintTimer $ when debugMode $ void $ do
              putStrLn ""
              putStrLn "After parallelizing"
              print $ pprMemModule repr_mod
            highLevelOptimizations times False SystemF.DimensionalitySimplifierPhase repr_mod
    else return repr_mod

  -- Sequentialize remaining loops
  repr_mod <- iterateM (highLevelOptimizations times False SystemF.SequentialSimplifierPhase) 6 repr_mod

  time times PrintTimer $ when debugMode $ void $ do
    putStrLn ""
    putStrLn "After Simplifying"
    print $ pprMemModule repr_mod
  
  -- Inline loops
  repr_mod <- iterateM (highLevelOptimizations times False SystemF.FinalSimplifierPhase) 2 repr_mod

  -- Final floating, to move repr dictionaries out of the way and ensure
  -- that copying is eliminated
  repr_mod <- time times FloatingTimer $ SystemF.longRangeFloating repr_mod

  -- Restructure the code resulting from inlining, which may create new
  -- local functions
  repr_mod <- iterateM (highLevelOptimizations times True SystemF.FinalSimplifierPhase) 3 repr_mod

  -- Eliminate case-of-case 
  repr_mod <- iterateM (highLevelOptimizations times True SystemF.PostFinalSimplifierPhase) 2 repr_mod

  -- Argument flattening
  time times PrintTimer $ when debugMode $ void $ do
    putStrLn ""
    putStrLn "Before Argument Flattening"
    print $ pprMemModule repr_mod
  repr_mod <- time times FlattenArgumentsTimer $
              SystemF.flattenArguments repr_mod
  
  time times PrintTimer $ when debugMode $ void $ do
    putStrLn "After argument flattening"
    print $ pprMemModule repr_mod
    evaluate $ SystemF.checkForShadowingModule repr_mod

  -- Reconstruct demand information after flattening variables,
  -- so that the next optimization pass can do more work
  repr_mod <- time times DemandTimer $ SystemF.localDemandAnalysis repr_mod
  repr_mod <- iterateM (highLevelOptimizations times True SystemF.PostFinalSimplifierPhase) 5 repr_mod

  time times PrintTimer $ when debugMode $ void $ do
    putStrLn ""
    putStrLn "Optimized"
    print $ pprMemModule repr_mod

  time times TypecheckTimer $ when debugMode $ void $ do
    SystemF.TypecheckMem.typeCheckModule repr_mod

  printTimes times

  ll_mod <- SystemF.lowerModule repr_mod
  ll_mod <- LowLevel.removeTrioletExports ll_mod
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
compilePyonAsmToGenC ll_mod ifaces c_file i_file h_file hxx_file = do
  when debugMode $ do
    evaluate $ LowLevel.checkDuplicateGlobalDefinitions ll_mod

  -- Low-level transformations
  ll_mod <- LowLevel.flattenRecordTypes ll_mod
  
  -- Link to interfaces
  ll_mod <- foldM (flip LowLevel.addInterfaceToModuleImports) ll_mod ifaces
  when debugMode $ void $ do
    putStrLn ""
    putStrLn "Lowered and flattened"
    print $ LowLevel.pprModule ll_mod
  
  when debugMode $ do
    evaluate $ LowLevel.checkDuplicateGlobalDefinitions ll_mod

  -- First round of optimizations: Simplify code
  ll_mod <- LowLevel.commonSubexpressionElimination ll_mod
  ll_mod <- return $ LowLevel.eliminateDeadCode ll_mod

  -- Several rounds of inlining and simplification.
  -- Run 2 rounds, which is enough to inline most HOFs.
  -- Then normalize tail calls to increase opportunities for inlining.
  let round m = do
        -- Label join points to help the inliner, then inline
        m <- LowLevel.convertJoinPoints m
        m <- LowLevel.Inlining2.inlineModule m
        -- Exploit optimization opportunities exposed by inlining
        m <- LowLevel.commonSubexpressionElimination m
        return $ LowLevel.eliminateDeadCode m

  ll_mod <- iterateM round 3 ll_mod
  ll_mod <- LowLevel.normalizeTailCalls ll_mod
  ll_mod <- iterateM round 2 ll_mod

  -- Cleanup
  ll_mod <- return $ LowLevel.clearImportedFunctionDefinitions ll_mod

  when debugMode $ void $ do
    putStrLn ""
    putStrLn "Optimized"
    print $ LowLevel.pprModule ll_mod  
  
  -- Generate interface file
  (ll_mod, ll_interface) <- LowLevel.createModuleInterface ll_mod
  writeFileAsByteString i_file $ encode ll_interface

  -- Closure conversion
  -- Remove any lambda values created by the last round of optimization
  when debugMode $ void $ do
    putStrLn ""
    putStrLn "Before closure conversion"
    print $ LowLevel.pprModule ll_mod
  ll_mod <- LowLevel.closureConvert ll_mod
  when debugMode $ void $ do
    putStrLn ""
    putStrLn "After closure conversion"
    print $ LowLevel.pprModule ll_mod

  when debugMode $ do
    evaluate $ LowLevel.checkDuplicateGlobalDefinitions ll_mod

  -- After closure conversion, cursors, owned pointers, and unit values
  -- are superfluous.  Convert pointer types and remove units.
  ll_mod <- LowLevel.insertReferenceTracking ll_mod
  ll_mod <- LowLevel.flattenRecordTypes ll_mod
  ll_mod <- LowLevel.removeUnits ll_mod

  when debugMode $ void $ do
    putStrLn ""
    putStrLn "After eliminating reference tracking"
    print $ LowLevel.pprModule ll_mod

  -- Second round of optimizations
  ll_mod <- LowLevel.commonSubexpressionElimination ll_mod
  ll_mod <- return $ LowLevel.eliminateDeadCode ll_mod
  ll_mod <- LowLevel.commonSubexpressionElimination ll_mod
  ll_mod <- return $ LowLevel.eliminateDeadCode ll_mod
  when debugMode $ void $ do
    putStrLn ""
    putStrLn "Final low-level code"
    print $ LowLevel.pprModule ll_mod  

  -- Generate and compile a C file
  c_mod <- LowLevel.generateCFile ll_mod
  writeFileAsString c_file c_mod
  
  -- Generate foreign language interfaces
  case LowLevel.generateCHeader ll_mod of
    Just h_mod -> writeFileAsString h_file h_mod
    Nothing -> return ()

  when (LowLevel.hasCXXExports ll_mod) $ do
    writeFileAsString hxx_file (LowLevel.Cxx.Wrappers.cxxHeader ll_mod)
    --writeFileWithHandle hxx_file (LowLevel.writeCxxHeader ll_mod)

-- | Compile a C file to produce an object file.
compileCFile c_fname o_fname = do
  include_path <- Paths.getDataFileName "include"
  let compiler_opts =
        [ "-c"                  -- Compile
        , "-g"                  -- Emit debug information
        , "-O3"                 -- Optimize
        , "-fno-strict-aliasing" -- Do not assume distinct types are unaliased
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
