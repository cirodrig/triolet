
{-# LANGUAGE TemplateHaskell, FlexibleInstances #-}
module Pyon.LowLevel.BuiltinsTH
where

import Language.Haskell.TH(Strict(..))
import Language.Haskell.TH.Syntax(Lift(..))

import Gluon.Common.THRecord
import Pyon.LowLevel.Syntax
import Pyon.LowLevel.Types
import Pyon.LowLevel.Record

instance Lift Signedness where
  lift x = let n = fromEnum x in [| toEnum n |]

instance Lift Size where
  lift x = let n = fromEnum x in [| toEnum n |]

instance Lift PrimType where
  lift UnitType = [| UnitType |]
  lift BoolType = [| BoolType |]
  lift (IntType sgn sz) = [| IntType sgn sz |]
  lift (FloatType sz) = [| FloatType sz |]
  lift PointerType = [| PointerType |]
  lift OwnedType = [| OwnedType |]

instance Lift (Field Int) where
  lift (Field off t) = [| Field off t |]

instance Lift (FieldType Int) where
  lift (PrimField pt) = [| PrimField pt |]
  lift (RecordField b rt) = [| RecordField b rt |]
  lift (BytesField s a) = [| BytesField s a |]

instance Lift (Record Int) where
  lift rec = let fields = map fieldType $ recordFields rec
             in [| staticRecord fields |] 

instance Lift ValueType where
  lift (PrimType pt) = [| PrimType pt |]
  lift (RecordType rt) = [| RecordType rt |] 

instance Lift FunctionType where
  lift ft
    | ftIsPrim ft    = [| primFunctionType params returns |]
    | ftIsClosure ft = [| closureFunctionType params returns |]
    where
      params = ftParamTypes ft
      returns = ftReturnTypes ft

-- | Predefined primitive functions
builtinPrimitives =
  [ ("alloc",
     primFunctionType [PrimType nativeWordType] [PrimType PointerType])
  , ("dealloc",
     primFunctionType [PrimType PointerType] [])
  , ("apply_pap",
     primFunctionType [PrimType OwnedType, PrimType PointerType] [])
  , ("free_pap",
     primFunctionType [PrimType PointerType] [])
  , ("free_lambda_closure",
     primFunctionType [PrimType PointerType] [])
  , ("free_letrec_closure",
     primFunctionType [PrimType PointerType] [])
  ]

closureBinaryFunctionType t = closureFunctionType [t, t] [t]

-- | Predefined closure functions
builtinFunctions =
  [ ("add_int",
     closureBinaryFunctionType $ PrimType pyonIntType)
  , ("sub_int",
     closureBinaryFunctionType $ PrimType pyonIntType)
  , ("add_float",
     closureBinaryFunctionType $ PrimType pyonFloatType)
  , ("sub_float",
     closureBinaryFunctionType $ PrimType pyonFloatType)
  , ("dealloc",
     closureFunctionType [PrimType PointerType] [])
  , ("copy4",
     closureFunctionType [PrimType PointerType, PrimType PointerType] [])
  , ("load_int",
     closureFunctionType [PrimType PointerType] [PrimType pyonIntType])
  , ("load_float",
     closureFunctionType [PrimType PointerType] [PrimType pyonFloatType])
  , ("load_NoneType",
     closureFunctionType [PrimType PointerType] [PrimType pyonNoneType])
  , ("store_int",
     closureFunctionType [PrimType pyonIntType, PrimType PointerType] [])
  , ("store_float",
     closureFunctionType [PrimType pyonFloatType, PrimType PointerType] [])
  , ("store_NoneType",
     closureFunctionType [PrimType pyonNoneType, PrimType PointerType] [])
  ]

-- | Predefined global data
builtinGlobals =
  []

lowLevelBuiltinsRecord = recordDef "LowLevelBuiltins" fields
  where
    prim_field (nm, _) = ("the_biprim_" ++ nm, IsStrict, [t| (Var, FunctionType) |])
    clo_field (nm, _) = ("the_bifun_" ++ nm, IsStrict, [t| (Var, EntryPoints) |])
    var_field (nm, _) = ("the_bivar_" ++ nm, IsStrict, [t| Var |])
    fields = map prim_field builtinPrimitives ++
             map clo_field builtinFunctions ++
             map var_field builtinGlobals
