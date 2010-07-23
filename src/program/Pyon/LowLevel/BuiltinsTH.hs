
{-# LANGUAGE TemplateHaskell, FlexibleInstances #-}
module Pyon.LowLevel.BuiltinsTH
where

import Language.Haskell.TH(Strict(..))
import Language.Haskell.TH.Syntax(Lift(..))

import Gluon.Common.THRecord
import qualified Pyon.SystemF.Builtins as SystemF
import Pyon.SystemF.Builtins(pyonBuiltin)
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

-- | Predefined closure functions and the core constructor they're derived
-- from.
builtinFunctions =
  [ -- Functions that do not exist in Core
    ("dealloc",
     Left $ closureFunctionType [PrimType PointerType] [])
  , ("copy4",
     Left $
     closureFunctionType [PrimType PointerType, PrimType PointerType] [])
    -- Functions translated from Core
  , ("add_int",
     Right [| pyonBuiltin (SystemF.addMember . SystemF.the_AdditiveDict_int) |])
  , ("sub_int", 
     Right [| pyonBuiltin (SystemF.subMember . SystemF.the_AdditiveDict_int) |])
  , ("add_float",
     Right [| pyonBuiltin (SystemF.addMember . SystemF.the_AdditiveDict_float) |])
  , ("sub_float",
     Right [| pyonBuiltin (SystemF.subMember . SystemF.the_AdditiveDict_float) |])
  , ("load_int",
     Right [| pyonBuiltin (SystemF.the_fun_load_int) |])
  , ("load_float",
     Right [| pyonBuiltin (SystemF.the_fun_load_float) |])
  , ("load_NoneType",
     Right [| pyonBuiltin (SystemF.the_fun_load_NoneType) |])
  , ("store_int",
     Right [| pyonBuiltin (SystemF.the_fun_store_int) |])
  , ("store_float",
     Right [| pyonBuiltin (SystemF.the_fun_store_float) |])
  , ("store_NoneType",
     Right [| pyonBuiltin (SystemF.the_fun_store_NoneType) |])
  ]

-- | Predefined global data
builtinGlobals =
  []

lowLevelBuiltinsRecord = recordDef "LowLevelBuiltins" fields
  where
    prim_field (nm, _) =
      ("the_biprim_" ++ nm, IsStrict, [t| (Var, FunctionType) |])
    clo_field (nm, _) =
      ("the_bifun_" ++ nm, IsStrict, [t| (Var, EntryPoints) |])
    var_field (nm, _) =
      ("the_bivar_" ++ nm, IsStrict, [t| Var |])
    fields = map prim_field builtinPrimitives ++
             map clo_field builtinFunctions ++
             map var_field builtinGlobals
