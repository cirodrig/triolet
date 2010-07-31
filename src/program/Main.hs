
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
import System.Posix.Temp

import Gluon.Eval.Error
import InitializeGlobals
import Parser.Driver
import Paths_pyon
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
import qualified LowLevel.Print as LowLevel
import qualified LowLevel.RecordFlattening as LowLevel
import qualified LowLevel.BuiltinCalls as LowLevel
import qualified LowLevel.Closures as LowLevel
import qualified LowLevel.ReferenceCounting as LowLevel
import qualified LowLevel.GenerateC as LowLevel

main = do
  -- Initialiation
  loadBuiltins
  initializeTIBuiltins
  
  args <- getArgs
  processCommandLine args 
  
processCommandLine args =
  case args
  of [filename] -> compileFile filename
     _ -> putStrLn "Expecting a filename as the only command-line parameter"

-- | Compile a pyon file.
-- 
-- This function consists chiefly of a long sequence of  compiler stages.
compileFile :: FilePath -> IO ()
compileFile fname = do
  unless (takeExtension fname == ".py") $ fail "Expecting a .py file"

  -- Parse and generate untyped code
  untyped_mod <- parseFile fname
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

  -- Convert to low-level form
  ll_mod <- Core.lower flat_mod
  
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
      o_fname = replaceExtension fname ".o"

  -- Write to a temporary file
  withTempFile "pyon.XXXXXX" $ \(c_fname, hdl) -> do
    hPutStr hdl c_mod
    hClose hdl
    
    -- Compile the file
    compileCFile c_fname o_fname
  
  return ()

-- | Compile a C file to produce an object file.
compileCFile c_fname o_fname = do
  include_path <- Paths_pyon.getDataFileName "include"
  let compiler_opts =
        [ "-c"                  -- Compile
        , "-g"                  -- Emit debug information
        , "-m32"                -- 32-bit mode
        , "-x", "c"             -- Source is a C file
        , c_fname               -- Input filename
        , "-o", o_fname         -- Output filename
        , "-I" ++ include_path  -- Include directory
        ]
  rc <- rawSystem "gcc" compiler_opts
  unless (rc == ExitSuccess) $ do
    putStrLn "Compilation failed: Error in C backend phase" 
    exitFailure

withTempFile template m = bracket (mkstemp template) close_file m
  where
    close_file (path, hdl) = do
      hClose hdl
      removeFile path
