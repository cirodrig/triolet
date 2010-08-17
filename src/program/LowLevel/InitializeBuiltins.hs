
{-# LANGUAGE TemplateHaskell #-}
module LowLevel.InitializeBuiltins(initializeLowLevelBuiltins)
where
  
import qualified Language.Haskell.TH as TH

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.THRecord
import GlobalVar
import LowLevel.Syntax
import LowLevel.Types
import LowLevel.BuiltinsTH
import LowLevel.Builtins
import LowLevel.Build
import LowLevel.FreshVar

-- This core module provides the low-level equivalent of core function types
import {-# SOURCE #-} Core.TypeLowering

initializePrimField :: IdentSupply Var -> ModuleName -> String -> FunctionType 
                    -> IO (Var, FunctionType)
initializePrimField supply mod nm fty =
  runFreshVarM supply $ do
    let lab = pgmLabel mod nm
        ext_name = if mod == builtinModuleName then Just nm else Nothing
    v <- newExternalVar lab ext_name (PrimType PointerType)
    return (v, fty)

initializeClosureField :: IdentSupply Var 
                       -> ModuleName
                       -> String
                       -> FunctionType
                       -> IO (Var, EntryPoints)
initializeClosureField supply mod nm fty =
  runFreshVarM supply $ do
    let lab = pgmLabel mod nm
        ext_name = if mod == builtinModuleName then Just nm else Nothing
    v <- newExternalVar lab ext_name (PrimType OwnedType)

    -- All builtin closures use the default closure deallocator
    ep <- mkEntryPoints CannotDeallocate fty (Just lab)
    return (v, ep)

initializeVarField :: IdentSupply Var 
                   -> ModuleName
                   -> String 
                   -> ValueType 
                   -> IO Var
initializeVarField supply mod nm ty =
  runFreshVarM supply $ do
    let lab = pgmLabel mod nm
        ext_name = if mod == builtinModuleName then Just nm else Nothing
    newExternalVar lab ext_name ty

{-
initializeGlobalField :: IdentSupply Var -> String -> ValueType -> IO Var
initializeGlobalField supply nm ty
  | typeOk ty =
      runFreshVarM supply $ do
        newBuiltinVar (builtinLabel nm) nm ty
  | otherwise =
      internalError "initializeGlobalField: unexpected type"
  where
    -- Global variables are used by reference, so they must have pointer type 
    -- or owned type
    typeOk (PrimType PointerType) = True
    typeOk (PrimType OwnedType) = True
    typeOk _ = False-}

initializeLowLevelBuiltins :: IdentSupply Var -> IO ()
initializeLowLevelBuiltins v_ids =
  initializeGlobalVar the_lowLevelBuiltins
    $(
      let closure_type :: Either FunctionType TH.ExpQ -> TH.ExpQ
          closure_type (Left t) = [| t |]
          closure_type (Right conQ) = [| conLoweredFunctionType $conQ |]
          init_primitives =
            [("the_biprim_" ++ nm, [| initializePrimField v_ids mod nm ty |]) 
            | (mod, nm, ty) <- builtinPrimitives]
          init_functions =
            [("the_bifun_" ++ nm,
              let fty = closure_type ty
              in [| initializeClosureField v_ids mod nm $fty |])
            | (mod, nm, ty) <- builtinFunctions]
          init_globals =
            [("the_bivar_" ++ nm, [| initializeVarField v_ids mod nm ty |]) 
            | (mod, nm, ty) <- builtinGlobals]
          inits = init_primitives ++ init_functions ++ init_globals
      in initializeRecordM lowLevelBuiltinsRecord inits)
