
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
  [ ("prim_alloc",
     primFunctionType [PrimType nativeWordType] [PrimType PointerType])
  , ("prim_dealloc",
     primFunctionType [PrimType PointerType] [])
  , ("prim_apply_pap",
     primFunctionType [PrimType OwnedType, PrimType PointerType] [])
  , ("prim_free_pap",
     primFunctionType [PrimType PointerType] [])
  , ("prim_free_lambda_closure",
     primFunctionType [PrimType PointerType] [])
  , ("prim_free_letrec_closure",
     primFunctionType [PrimType PointerType] [])
  ]

-- | Predefined closure functions
builtinFunctions =
  [ ("fun_dealloc",
     closureFunctionType [PrimType PointerType] [])
  , ("fun_copy4",
     closureFunctionType [PrimType PointerType, PrimType PointerType] [])
  , ("fun_load_int",
     closureFunctionType [PrimType OwnedType] [PrimType pyonIntType])
  , ("fun_load_float",
     closureFunctionType [PrimType OwnedType] [PrimType pyonFloatType])
  , ("fun_load_NoneType",
     closureFunctionType [PrimType OwnedType] [PrimType pyonNoneType])
  , ("fun_store_int",
     closureFunctionType [PrimType pyonIntType] [PrimType OwnedType])
  , ("fun_store_float",
     closureFunctionType [PrimType pyonFloatType] [PrimType OwnedType])
  , ("fun_store_NoneType",
     closureFunctionType [PrimType pyonNoneType] [PrimType OwnedType])
  ]

-- | Predefined global data
builtinGlobals =
  []

lowLevelBuiltinsRecord = recordDef "LowLevelBuiltins" fields
  where
    prim_field (nm, _) = ("the_" ++ nm, IsStrict, [t| (Var, FunctionType) |])
    clo_field (nm, _) = ("the_" ++ nm, IsStrict, [t| (Var, EntryPoints) |])
    var_field (nm, _) = ("the_" ++ nm, IsStrict, [t| Var |])
    fields = map prim_field builtinPrimitives ++
             map clo_field builtinFunctions ++
             map var_field builtinGlobals
