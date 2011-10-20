{-| Additional data types used in code.

/Value types/ are data types that can be stored in local variables.
Function types are the type signatures of functions.
-}

module LowLevel.CodeTypes
       (module LowLevel.Types,
        module LowLevel.Record,
        ValueType(..),
        valueToPrimType,
        valueToFieldType,
        CallConvention(..),
        FunctionType,
        primFunctionType,
        joinFunctionType,
        closureFunctionType,
        mkFunctionType,
        ftIsPrim,
        ftIsClosure,
        ftConvention,
        ftParamTypes,
        ftReturnTypes
       )
where

import Common.Error
import LowLevel.Types
import LowLevel.Record
import {-# SOURCE #-} LowLevel.Syntax

-- | A type that may be put into a variable
data ValueType = PrimType !PrimType
               | RecordType !StaticRecord
                 deriving(Eq, Ord)

instance HasSize ValueType where
  sizeOf (PrimType pt) = sizeOf pt
  sizeOf (RecordType rt) = sizeOf rt
  alignOf (PrimType pt) = alignOf pt
  alignOf (RecordType rt) = alignOf rt
  pointerlessness (PrimType pt) = pointerlessness pt
  pointerlessness (RecordType rt) = pointerlessness rt

valueToPrimType :: ValueType -> PrimType
valueToPrimType (PrimType pt) = pt
valueToPrimType _ =
  internalError "Expecting a primitive type, got a record type"

valueToFieldType :: ValueType -> StaticFieldType
valueToFieldType (PrimType pt) = PrimField pt
valueToFieldType (RecordType rt) = RecordField rt

-- | A function calling convention
data CallConvention =
    -- | Primitive calling conventions using the C ABI.
    --   Primitive calls are compiled to machine-level function calls.
    --   Functions that use this convention must be global.
    PrimCall
    -- | Closure-based calling convention.  A call becomes constructing and
    --   entering a closure.  Closure functions may be applied to fewer or  
    --   more arguments than they expect.  Closure functions may be global or
    --   local.  This convention is not used after closure conversion.
  | ClosureCall
    -- | Control flow join points.  Join points must local functions, and
    --   calls to join points must be tail calls.
    --   A call compiles to an unconditional branch.
    --   A join point must be defined in the same function where it is
    --   used or in a join point of the function where it is used.
  | JoinCall
  deriving(Eq, Enum, Bounded)

-- | A primitive or closure function type.
data FunctionType =
  FunctionType !CallConvention ![ValueType] ![ValueType]
  deriving(Eq)

primFunctionType :: [ValueType] -> [ValueType] -> FunctionType
primFunctionType params returns = FunctionType PrimCall params returns

closureFunctionType :: [ValueType] -> [ValueType] -> FunctionType
closureFunctionType params returns = FunctionType ClosureCall params returns

joinFunctionType :: [ValueType] -> [ValueType] -> FunctionType
joinFunctionType params returns = FunctionType JoinCall params returns

mkFunctionType :: CallConvention -> [ValueType] -> [ValueType] -> FunctionType
mkFunctionType = FunctionType

ftIsPrim, ftIsClosure :: FunctionType -> Bool
ftIsPrim (FunctionType PrimCall _ _) = True
ftIsPrim _ = False
ftIsClosure (FunctionType ClosureCall _ _) = True
ftIsClosure _ = False

ftConvention :: FunctionType -> CallConvention
ftConvention (FunctionType c _ _) = c

ftParamTypes :: FunctionType -> [ValueType]
ftParamTypes (FunctionType _ ps _) = ps

ftReturnTypes :: FunctionType -> [ValueType]
ftReturnTypes (FunctionType _ _ rs) = rs

