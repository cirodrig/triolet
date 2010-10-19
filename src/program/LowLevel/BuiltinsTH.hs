
{-# LANGUAGE TemplateHaskell, FlexibleInstances #-}
module LowLevel.BuiltinsTH
where

import Language.Haskell.TH(Strict(..))
import Language.Haskell.TH.Syntax(Lift(..))

import Gluon.Common.Error
import Gluon.Common.Label
import Gluon.Common.THRecord
import qualified SystemF.Builtins as SystemF
import SystemF.Builtins(pyonBuiltin)
import LowLevel.Syntax
import LowLevel.Types
import LowLevel.Record

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
  lift (RecordField rt) = [| RecordField rt |]
  lift (BytesField s a) = [| BytesField s a |]
  lift (AlignField n) = [| AlignField n |]

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
    | otherwise      = internalError "FunctionType.lift"
    where
      params = ftParamTypes ft
      returns = ftReturnTypes ft

-- | A 'BuiltinVarName' controls what name is assigned to a built-in variable. 
data BuiltinVarName =
    -- | Use the string as the external name
    CName { builtinVarModuleName :: ModuleName 
          , builtinVarUnqualifiedName :: String
          }
    -- | No external name
  | PyonName { builtinVarModuleName :: ModuleName 
             , builtinVarUnqualifiedName :: String
             }

instance Lift BuiltinVarName where
  lift (CName nm s) = [| CName nm s |]
  lift (PyonName nm s) = [| PyonName nm s |]

biName = CName builtinModuleName

-- | Predefined primitive functions
builtinPrimitives =
  [ -- debug.c
    (biName "pyon_db_int",
     primFunctionType [PrimType nativeIntType] [])
  , (biName "pyon_db_word",
     primFunctionType [PrimType nativeWordType] [])
  , (biName "pyon_db_pointer",
     primFunctionType [PrimType PointerType] [])
    -- memory.c
  , (biName "pyon_alloc",
     primFunctionType [PrimType nativeWordType] [PrimType PointerType])
  , (biName "pyon_dealloc",
     primFunctionType [PrimType PointerType] [])
    -- apply.c
  , (biName "apply_i32_f",
     primFunctionType [ PrimType OwnedType
                      , PrimType (IntType Unsigned S32)] [PrimType OwnedType])
  , (biName "apply_i32",
     primFunctionType [PrimType OwnedType
                      , PrimType (IntType Unsigned S32)
                      , PrimType PointerType] [])
  , (biName "apply_f32_f",
     primFunctionType [ PrimType OwnedType
                      , PrimType (FloatType S32)] [PrimType OwnedType])
  , (biName "apply_f32",
     primFunctionType [PrimType OwnedType
                      , PrimType (FloatType S32)
                      , PrimType PointerType] [])
  , (biName "apply_o_f",
     primFunctionType [ PrimType OwnedType
                      , PrimType OwnedType] [PrimType OwnedType])
  , (biName "apply_o",
     primFunctionType [PrimType OwnedType
                      , PrimType OwnedType
                      , PrimType PointerType] [])
  , (biName "free_pap",
     primFunctionType [PrimType PointerType] [])
  ]

closureBinaryFunctionType t = closureFunctionType [t, t] [t]

module_prim = moduleName "pyon.internal.prim"
module_memory_py = moduleName "pyon.internal.memory_py"
module_stream = moduleName "pyon.internal.stream"
module_structures = moduleName "pyon.internal.structures"
module_list = moduleName "pyon.internal.list"

-- | Predefined closure functions and the core constructor they're derived
-- from.
builtinFunctions =
  [ -- Functions that do not exist in Core
    -- memory_py.pyasm
    (PyonName module_memory_py "deallocF",
     Left $ closureFunctionType [PrimType PointerType] [])
  , (CName module_memory_py "dummy_finalizer",
     Left $ closureFunctionType [PrimType PointerType] [])
  , (CName module_memory_py "copy1F",
     Left $
     closureFunctionType [PrimType PointerType, PrimType PointerType] [])
  , (CName module_memory_py "copy2F",
     Left $
     closureFunctionType [PrimType PointerType, PrimType PointerType] [])
  , (CName module_memory_py "copy4F",
     Left $
     closureFunctionType [PrimType PointerType, PrimType PointerType] [])

    -- Functions translated from Core
  , (PyonName module_memory_py "copy",
     Right [| pyonBuiltin (SystemF.the_fun_copy) |])
  , (PyonName module_list "list_build",
     Right [| pyonBuiltin (SystemF.buildMember . SystemF.the_TraversableDict_list) |])
  , (PyonName module_list "list_traverse",
     Right [| pyonBuiltin (SystemF.traverseMember . SystemF.the_TraversableDict_list) |])
  , (PyonName module_stream "Stream_bind",
     Right [| pyonBuiltin (SystemF.the_oper_CAT_MAP) |])
  , (PyonName module_stream "Stream_return",
     Right [| pyonBuiltin (SystemF.the_fun_return) |])
  , (PyonName module_structures "additiveDict",
     Right [| pyonBuiltin (SystemF.the_additiveDict) |])
    
    -- Functions that are replaced by primitive operations
  , (PyonName builtinModuleName "eq_int",
     Right [| pyonBuiltin (SystemF.eqMember . SystemF.the_EqDict_int) |])
  , (PyonName builtinModuleName "ne_int",
     Right [| pyonBuiltin (SystemF.neMember . SystemF.the_EqDict_int) |])
  , (PyonName builtinModuleName "eq_float",
     Right [| pyonBuiltin (SystemF.eqMember . SystemF.the_EqDict_float) |])
  , (PyonName builtinModuleName "ne_float",
     Right [| pyonBuiltin (SystemF.neMember . SystemF.the_EqDict_float) |])
  , (PyonName module_prim "zero_int",
     Right [| pyonBuiltin (SystemF.zeroMember . SystemF.the_AdditiveDict_int) |])
  , (PyonName module_prim "add_int",
     Right [| pyonBuiltin (SystemF.addMember . SystemF.the_AdditiveDict_int) |])
  , (PyonName module_prim "sub_int", 
     Right [| pyonBuiltin (SystemF.subMember . SystemF.the_AdditiveDict_int) |])
  , (PyonName builtinModuleName "zero_float",
     Right [| pyonBuiltin (SystemF.zeroMember . SystemF.the_AdditiveDict_float) |])
  , (PyonName builtinModuleName "add_float",
     Right [| pyonBuiltin (SystemF.addMember . SystemF.the_AdditiveDict_float) |])
  , (PyonName builtinModuleName "sub_float",
     Right [| pyonBuiltin (SystemF.subMember . SystemF.the_AdditiveDict_float) |])
  , (PyonName builtinModuleName "load_int",
     Right [| pyonBuiltin (SystemF.the_fun_load_int) |])
  , (PyonName builtinModuleName "load_float",
     Right [| pyonBuiltin (SystemF.the_fun_load_float) |])
  , (PyonName builtinModuleName "load_bool",
     Right [| pyonBuiltin (SystemF.the_fun_load_bool) |])
  , (PyonName builtinModuleName "load_NoneType",
     Right [| pyonBuiltin (SystemF.the_fun_load_NoneType) |])
  , (PyonName builtinModuleName "store_int",
     Right [| pyonBuiltin (SystemF.the_fun_store_int) |])
  , (PyonName builtinModuleName "store_float",
     Right [| pyonBuiltin (SystemF.the_fun_store_float) |])
  , (PyonName builtinModuleName "store_bool",
     Right [| pyonBuiltin (SystemF.the_fun_store_bool) |])
  , (PyonName builtinModuleName "store_NoneType",
     Right [| pyonBuiltin (SystemF.the_fun_store_NoneType) |])
  ]

-- | Predefined global data
builtinGlobals =
  [ -- Info tables
    (biName "pap_info", PrimType PointerType)
  , (biName "global_closure_info", PrimType PointerType)
    -- Physical representations of data types
  , (PyonName module_structures "int_pass_conv", PrimType PointerType)
  , (biName "float_pass_conv", PrimType PointerType)
  , (biName "bool_pass_conv", PrimType PointerType)
  , (PyonName module_structures "AdditiveDict_pass_conv", PrimType PointerType)
  , (biName "PassConv_pass_conv", PrimType PointerType)
  ]

lowLevelBuiltinsRecord = recordDef "LowLevelBuiltins" fields
  where
    prim_field (nm, _) =
      ("the_biprim_" ++ builtinVarUnqualifiedName nm, IsStrict,
       [t| (Var, FunctionType) |])
    clo_field (nm, _) =
      ("the_bifun_" ++ builtinVarUnqualifiedName nm, IsStrict,
       [t| (Var, EntryPoints) |])
    var_field (nm, _) =
      ("the_bivar_" ++ builtinVarUnqualifiedName nm, IsStrict, [t| Var |])
    fields = map prim_field builtinPrimitives ++
             map clo_field builtinFunctions ++
             map var_field builtinGlobals
