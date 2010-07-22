{-| Information about low-level builtin symbols.
-}

{-# LANGUAGE TemplateHaskell #-}
module Pyon.LowLevel.Builtins(builtinType)
where

import qualified Data.IntMap as IntMap
import System.IO.Unsafe

import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.THRecord
import Gluon.Core(Con(..))
import Pyon.LowLevel.Syntax
import Pyon.LowLevel.Types
import Pyon.LowLevel.BuiltinsTH
import Pyon.LowLevel.Build(FreshVarM, runFreshVarM)
import qualified Pyon.SystemF.Builtins as SystemF
import Pyon.Globals

$(sequence [declareRecord lowLevelBuiltinsRecord])

-- | Get the low-level type of a constructor
builtinType :: Con -> Maybe PrimType
builtinType c = IntMap.lookup (fromIdent $ conID c) builtinTypesTable

builtinTypesTable =
  IntMap.fromList [(fromIdent $ conID c, t) | (c, t) <- tbl]
  where
    tbl = []

initializePrimField :: String -> FunctionType -> IO (Var, FunctionType)
initializePrimField nm fty =
  withTheLLVarIdentSupply $ \supply -> runFreshVarM supply $ do
    let lab = builtinLabel nm
    v <- newVar (Just lab) (PrimType PointerType)
    return (v, fty)

initializeClosureField :: String -> FunctionType -> IO (Var, EntryPoints)
initializeClosureField nm fty =
  withTheLLVarIdentSupply $ \supply -> runFreshVarM supply $ do
    let lab = builtinLabel nm
    v <- newVar (Just lab) (PrimType OwnedType)
    ep <- mkEntryPoints fty (Just lab)
    return (v, ep)

initializeVarField :: String -> ValueType -> IO Var
initializeVarField nm ty =
  withTheLLVarIdentSupply $ \supply -> runFreshVarM supply $ do
    newVar (Just $ builtinLabel nm) ty

-- | The low-level built-in global variables
lowLevelBuiltins :: LowLevelBuiltins
{-# NOINLINE lowLevelBuiltins #-}
lowLevelBuiltins =
  unsafePerformIO $(
    let init_primitives =
          [("the_" ++ nm, [| initializePrimField nm ty |]) 
          | (nm, ty) <- builtinPrimitives]
        init_functions =
          [("the_" ++ nm, [| initializeClosureField nm ty |])
          | (nm, ty) <- builtinFunctions]
        init_globals =
          [("the_" ++ nm, [| initializeVarField nm ty |]) 
          | (nm, ty) <- builtinGlobals]
        inits = init_primitives ++ init_functions ++ init_globals
    in initializeRecordM lowLevelBuiltinsRecord inits)
