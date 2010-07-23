
{-# LANGUAGE TemplateHaskell #-}
module Pyon.LowLevel.InitializeBuiltins(initializeLowLevelBuiltins)
where
  
import Control.Concurrent.MVar
import qualified Language.Haskell.TH as TH
import System.IO.Unsafe

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.MonadLogic
import Gluon.Common.THRecord
import Gluon.Core(Con(..))
import Pyon.LowLevel.Syntax
import Pyon.LowLevel.Types
import Pyon.LowLevel.Record
import Pyon.LowLevel.BuiltinsTH
import Pyon.LowLevel.Builtins
import Pyon.LowLevel.FreshVar

import qualified Pyon.SystemF.Builtins as SystemF

-- This core module provides the low-level equivalent of core function types
import {-# SOURCE #-} Pyon.Core.TypeLowering

initializePrimField :: IdentSupply Var -> String -> FunctionType 
                    -> IO (Var, FunctionType)
initializePrimField supply nm fty =
  runFreshVarM supply $ do
    let lab = builtinLabel nm
    v <- newBuiltinVar lab (PrimType PointerType)
    return (v, fty)

initializeClosureField :: IdentSupply Var 
                       -> String
                       -> FunctionType
                       -> IO (Var, EntryPoints)
initializeClosureField supply nm fty =
  runFreshVarM supply $ do
    let lab = builtinLabel nm
    v <- newBuiltinVar lab (PrimType OwnedType)
    ep <- mkEntryPoints fty (Just lab)
    return (v, ep)

initializeVarField :: IdentSupply Var -> String -> ValueType -> IO Var
initializeVarField supply nm ty =
  runFreshVarM supply $ do
    newBuiltinVar (builtinLabel nm) ty

initializeLowLevelBuiltins :: IdentSupply Var -> IO ()
initializeLowLevelBuiltins v_ids = do
  bi <- $(
    let closure_type :: Either FunctionType TH.ExpQ -> TH.ExpQ
        closure_type (Left t) = [| t |]
        closure_type (Right conQ) = [| conLoweredFunctionType $conQ |]
        init_primitives =
          [("the_biprim_" ++ nm, [| initializePrimField v_ids nm ty |]) 
          | (nm, ty) <- builtinPrimitives]
        init_functions =
          [("the_bifun_" ++ nm,
            let fty = closure_type ty
            in [| initializeClosureField v_ids nm $fty |])
          | (nm, ty) <- builtinFunctions]
        init_globals =
          [("the_bivar_" ++ nm, [| initializeVarField v_ids nm ty |]) 
          | (nm, ty) <- builtinGlobals]
        inits = init_primitives ++ init_functions ++ init_globals
    in initializeRecordM lowLevelBuiltinsRecord inits)
        
  ok <- tryPutMVar lowLevelBuiltins_var bi
  if ok then return ()
    else fail "initializeLowLevelBuiltins: Already initialized"
