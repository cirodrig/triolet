
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
import qualified SystemF.ConSpecialization as SystemF
import qualified SystemF.PartialEval as SystemF
import qualified SystemF.DeadCodeSF
import qualified SystemF.DemandAnalysis as SystemF
import qualified SystemF.GlobalDemand as SystemF
import qualified SystemF.ElimPatternMatching as SystemF
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
import qualified LowLevel.CSE as LowLevel
import qualified LowLevel.Closures as LowLevel
import qualified LowLevel.DeadCode as LowLevel
import qualified LowLevel.ReferenceCounting as LowLevel
import qualified LowLevel.GenerateC as LowLevel
import qualified LowLevel.GenerateCHeader as LowLevel
import qualified LowLevel.GenerateCXXHeader as LowLevel
import qualified LowLevel.Inlining as LowLevel
import qualified LowLevel.Inlining2
import qualified LowLevel.JoinPoints as LowLevel
import qualified LowLevel.InterfaceFile as LowLevel
import qualified LLParser.Parser as LLParser
import qualified LLParser.TypeInference as LLParser
import qualified LLParser.GenLowLevel2 as LLParser
import qualified Globals
import GlobalVar

debugMode = False

main = do
  -- Parse arguments
  (global_values, job) <- parseCommandLineArguments

  -- Initialiation
  loadBuiltins global_values
  initializeTIBuiltins
  
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
highLevelOptimizations :: Bool
                       -> SystemF.SimplifierPhase
                       -> SystemF.Module SystemF.Mem
                       -> IO (SystemF.Module SystemF.Mem)
highLevelOptimizations global_demand_analysis simplifier_phase mod = do
  mod <- SystemF.rewriteAtPhase simplifier_phase mod
  when debugMode $ void $ do
    putStrLn "After rewrite"
    print $ SystemF.PrintMemoryIR.pprModule mod
    evaluate $ SystemF.checkForShadowingModule mod -- DEBUG
    SystemF.TypecheckMem.typeCheckModule mod

  mod <- if global_demand_analysis
         then SystemF.demandAnalysis mod
         else SystemF.localDemandAnalysis mod

  -- Temporary: specialize on constructors and re-run demand analysis
  mod <- SystemF.specializeOnConstructors mod
  mod <- if global_demand_analysis
         then SystemF.demandAnalysis mod
         else SystemF.localDemandAnalysis mod
  
  return mod

-- | Compile a pyon file from source code to high-level, unoptimized code.
compilePyonToPyonMem :: CompileFlags -> FilePath -> String
                     -> IO (SystemF.Module SystemF.Mem)
compilePyonToPyonMem compile_flags path text = do
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

  -- Re-run partial evaluation to simplify the specialized code.
  sf_mod <- return $ SystemF.partialEvaluateModule sf_mod
  putStrLn ""
  putStrLn "System F"
  print $ SystemF.pprModule sf_mod

  -- Convert to explicit memory representation
  repr_mod <- SystemF.representationInference sf_mod
  
  -- Add predefined functions to the module
  repr_mod <- SystemF.insertGlobalSystemFFunctions repr_mod
  
  putStrLn ""
  putStrLn "Memory IR"
  print $ SystemF.PrintMemoryIR.pprModule repr_mod
  when debugMode $ void $ do
    SystemF.TypecheckMem.typeCheckModule repr_mod -- DEBUG
  
  return repr_mod

compilePyonMemToPyonAsm :: CompileFlags -> SystemF.Module SystemF.Mem
                        -> IO LowLevel.Module
compilePyonMemToPyonAsm compile_flags repr_mod = do

  -- General-purpose, high-level optimizations
  repr_mod <- highLevelOptimizations True SystemF.GeneralSimplifierPhase repr_mod

  repr_mod <- SystemF.longRangeFloating repr_mod
  when debugMode $ void $ do
    putStrLn "After floating 1"
    print $ SystemF.PrintMemoryIR.pprModule repr_mod
    evaluate $ SystemF.checkForShadowingModule repr_mod -- DEBUG

  repr_mod <- highLevelOptimizations True SystemF.GeneralSimplifierPhase repr_mod
  repr_mod <- iterateM (highLevelOptimizations False SystemF.GeneralSimplifierPhase) 4 repr_mod
  
  -- Parallelize outer loops
  repr_mod <-
    if lookupCompileFlag DoParallelization compile_flags  
    then do repr_mod <- SystemF.parallelLoopRewrite repr_mod
            highLevelOptimizations False SystemF.GeneralSimplifierPhase repr_mod
    else return repr_mod

  -- Sequentialize remaining loops
  repr_mod <- iterateM (highLevelOptimizations False SystemF.SequentialSimplifierPhase) 4 repr_mod

  putStrLn ""
  putStrLn "After Simplifying"
  print $ SystemF.PrintMemoryIR.pprModule repr_mod
  
  -- Inline loops
  repr_mod <- highLevelOptimizations False SystemF.FinalSimplifierPhase repr_mod

  repr_mod <- SystemF.longRangeFloating repr_mod
  when debugMode $ void $ do
    putStrLn "After floating 2"
    print $ SystemF.PrintMemoryIR.pprModule repr_mod
    evaluate $ SystemF.checkForShadowingModule repr_mod -- DEBUG

  -- Restructure the code resulting from inlining, which may create new
  -- local functions
  repr_mod <- highLevelOptimizations True SystemF.FinalSimplifierPhase repr_mod
  repr_mod <- highLevelOptimizations True SystemF.FinalSimplifierPhase repr_mod

  -- Argument flattening
  putStrLn ""
  putStrLn "Before Argument Flattening"
  print $ SystemF.PrintMemoryIR.pprModule repr_mod
  repr_mod <- SystemF.performGlobalDemandAnalysis repr_mod
  repr_mod <- SystemF.flattenArguments repr_mod
  
  when debugMode $ void $ do
    putStrLn "After argument flattening"
    print $ SystemF.PrintMemoryIR.pprModule repr_mod
    evaluate $ SystemF.checkForShadowingModule repr_mod -- DEBUG
  tc_repr_mod <- SystemF.TypecheckMem.typeCheckModule repr_mod

  -- Reconstruct demand information after flattening variables,
  -- so that the next optimization pass can do more work
  repr_mod <- SystemF.localDemandAnalysis repr_mod
  repr_mod <- iterateM (highLevelOptimizations True SystemF.FinalSimplifierPhase) 5 repr_mod

  putStrLn ""
  putStrLn "Optimized"
  print $ SystemF.PrintMemoryIR.pprModule repr_mod

  tc_repr_mod <- SystemF.TypecheckMem.typeCheckModule repr_mod
  ll_mod <- SystemF.lowerModule tc_repr_mod
  
  {- This is the old optimization sequence
  print "Generating memory IR"
  mem_mod <- SystemF.generateMemoryIR tc_mod
  
  putStrLn "Memory"
  print $ SystemF.PrintMemoryIR.pprModule mem_mod
  
  -- Optimizations on memory representation.
  -- The first group of optimizations performs inlining to create bigger 
  -- functions, then floating and dead code elimination.  These steps 
  -- are primarily setup to improve the accuracy of the simplifier.
  mem_mod <- highLevelOptimizations True False mem_mod

  -- The next group of optimizations does the main set of optimizations,
  -- including high-level transformations via rewriting.
  -- Currently there are inter-pass dependences that we
  -- stupidly resolve by running them lots of times.
  mem_mod <- highLevelOptimizations True False mem_mod
  mem_mod <- iterateM (highLevelOptimizations False False) 6 mem_mod

  -- Parallelize loops, then sequentialize the remaining loops
  mem_mod <-
    if lookupCompileFlag DoParallelization compile_flags  
    then do mem_mod <- SystemF.parallelLoopRewrite mem_mod
            highLevelOptimizations False False mem_mod
    else return mem_mod

  mem_mod <- iterateM (highLevelOptimizations False True) 2 mem_mod
  putStrLn "Loop rewritten"
  print $ SystemF.PrintMemoryIR.pprModule mem_mod

  -- Flatten function arguments and local variables.
  -- We transform arguments and returns first, then run a simplifier pass 
  -- to rebuild demand information.
  -- Argument flattening leads to more precise demand information,
  -- which makes local variable flattening more effective.
  --
  -- Loop through this twice because some streams are still being
  -- converted to loops at this point.  This issue should really be fixed
  -- by improving the optimizations that come before this point.
  let flatten_variables mod = do
        mod <- SystemF.flattenArguments mod
        mod <- highLevelOptimizations False True mod
        mod <- SystemF.flattenLocals mod

        -- Simplify the code that was introduced by flattening. 
        -- Flattening also enables more value propagation and rewrites, which
        -- may expose more opportunities for flattening.
        mod <- iterateM (highLevelOptimizations False True) 4 mod
        return mod

  mem_mod <- iterateM flatten_variables 3 mem_mod

  putStrLn "Optimized Memory"
  print $ SystemF.PrintMemoryIR.pprModule mem_mod

  -- Lower
  tc_mem_mod <- SystemF.TypecheckMem.typeCheckModule mem_mod
  --SystemF.inferSideEffects tc_mod
  ll_mod <- SystemF.lowerModule tc_mem_mod
  -}

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
compilePyonAsmToGenC ll_mod ifaces c_file i_file h_file hxx_file = do
  print $ LowLevel.pprModule ll_mod
  -- Low-level transformations
  ll_mod <- LowLevel.flattenRecordTypes ll_mod
  
  -- Link to interfaces
  ll_mod <- foldM (flip LowLevel.addInterfaceToModuleImports) ll_mod ifaces
  putStrLn ""
  putStrLn "Lowered and flattened"
  print $ LowLevel.pprModule ll_mod
  
  -- First round of optimizations: Simplify code
  ll_mod <- LowLevel.commonSubexpressionElimination ll_mod
  ll_mod <- return $ LowLevel.eliminateDeadCode ll_mod

  -- Label join points, then inline
  ll_mod <- LowLevel.convertJoinPoints ll_mod
  ll_mod <- LowLevel.Inlining2.inlineModule ll_mod

  -- Additional rounds: more inlining
  ll_mod <- iterateM (LowLevel.commonSubexpressionElimination >=>
                      return . LowLevel.eliminateDeadCode >=>
                      LowLevel.Inlining2.inlineModule) 5 ll_mod

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
  putStrLn ""
  putStrLn "Before closure conversion"
  print $ LowLevel.pprModule ll_mod
  ll_mod <- LowLevel.closureConvert ll_mod
  putStrLn ""
  putStrLn "After closure conversion"
  print $ LowLevel.pprModule ll_mod
  ll_mod <- LowLevel.insertReferenceCounting ll_mod
  
  -- Second round of optimizations
  ll_mod <- LowLevel.commonSubexpressionElimination ll_mod
  ll_mod <- return $ LowLevel.eliminateDeadCode ll_mod
  -- FIXME: Why do we need to call 'eliminateDeadCode' twice to
  -- get the job done?
  ll_mod <- return $ LowLevel.eliminateDeadCode ll_mod
  putStrLn ""
  putStrLn "Second optimization pass"
  print $ LowLevel.pprModule ll_mod  

  -- Generate and compile a C file
  c_mod <- LowLevel.generateCFile ll_mod
  writeFileAsString c_file c_mod
  
  -- Generate foreign language interfaces
  case LowLevel.generateCHeader ll_mod of
    Just h_mod -> writeFileAsString h_file h_mod
    Nothing -> return ()

  when (LowLevel.hasCXXExports ll_mod) $ do
    writeFileWithHandle hxx_file (LowLevel.writeCxxHeader ll_mod)

-- | Compile a C file to produce an object file.
compileCFile c_fname o_fname = do
  include_path <- Paths.getDataFileName "include"
  let compiler_opts =
        [ "-c"                  -- Compile
        , "-g"                  -- Emit debug information
        , "-O2"                 -- Optimize
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
