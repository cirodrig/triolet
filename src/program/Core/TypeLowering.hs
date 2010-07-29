{-| Lowering of types from cor representation to low-level representation.

These routines are used to keep track of type information while lowering a 
program from core to low-level representation.  Lowering has to compute the
types of functions and function return values in order to generate correct 
low-level code.

There are also some functions used to compute a function's low-level type 
from its core type.  These functions are used to initialize the low-level
builtin functions.
-}

module Core.TypeLowering
where

import Gluon.Common.Error
import Gluon.Core
import SystemF.Builtins
import Core.Syntax
import Core.BuiltinTypes
import LowLevel.Syntax as LL
import LowLevel.Types as LL
import LowLevel.Record as LL
import LowLevel.Builtins as LL

-- | During lowering, expressions are annotated with either a core type
-- or a low-level type.
--
-- At function calls, the core types of the function and any dependent
-- parameters are needed in order to compute the function's return type.
-- In the scrutinee of a case statement, the core type is used to determine
-- how to convert the case statement.
--
-- When a value is known not to be used dependently, or is inserted by the
-- translation, we can safely use the value type.  In general, we use the 
-- core type unless the value doesn't have a core type.
data LoweringType = 
    CoreType !(CBind CReturnT Rec)
  | LLType !LL.ValueType

lowered :: LoweringType -> LL.ValueType
lowered (LLType vt)   = vt
lowered (CoreType ct) = lowerExpressionType ct

-- | Get the low-level value type used to pass the given core type by value.
valueType :: RCType -> LL.ValueType
valueType core_type =
  case unpackConAppCT core_type
  of Just (con, args)
       | con `isPyonBuiltin` the_int -> LL.PrimType $ IntType Signed S32
       | con `isPyonBuiltin` the_float -> LL.PrimType $ FloatType S32
       | con `isPyonBuiltin` the_bool -> LL.PrimType BoolType
       | con `isPyonBuiltin` the_NoneType -> LL.PrimType UnitType
       | con `isPyonBuiltin` the_PassConv -> LL.RecordType LL.passConvRecord
     _ -> case core_type
          of ExpCT (LitE {expLit = KindL _}) -> LL.PrimType UnitType
             _ -> internalError $ "valueType: Unexpected type"

-- | Get the value type that will be used to pass the given core type.
lowerExpressionType :: CBind CReturnT Rec -> LL.ValueType
lowerExpressionType (core_binder ::: core_type) =
  case core_binder
  of ValRT -> valueType core_type
     OwnRT -> LL.PrimType OwnedType
     WriteRT -> LL.PrimType PointerType
     ReadRT _ -> LL.PrimType PointerType

-- | Translate the core function type to a low-level function type.
lowerFunctionType :: RCFunType -> LL.FunctionType
lowerFunctionType ft = lower_ft id ft
  where
    lower_ft params_hd ft =
      case ft
      of ArrCT {ctParam = param_binder ::: param_type, ctRange = rng} ->
           let ll_param_type =
                 case param_binder
                 of ValPT _ -> valueType param_type
                    OwnPT -> LL.PrimType LL.OwnedType
                    ReadPT _ -> LL.PrimType LL.PointerType
           in lower_ft (params_hd . (ll_param_type :)) rng
         RetCT {ctReturn = ret_binder ::: ret_type} ->
           case ret_binder
           of ValRT -> return_value $ valueType ret_type
              OwnRT -> return_value $ LL.PrimType LL.OwnedType
              WriteRT -> return_in_param
              ReadRT _ -> return_value $ LL.PrimType LL.PointerType
      where
        -- The low-level function returns a value of the given type
        return_value rt =
          LL.closureFunctionType (params_hd []) [rt]
          
        -- The low-level function takes an extra parameter, to which it writes
        -- its return value
        return_in_param =
          LL.closureFunctionType (params_hd [LL.PrimType LL.PointerType]) []

conLoweredFunctionType :: Con -> LL.FunctionType
conLoweredFunctionType c =
  case conCoreType c
  of FunCT ft -> lowerFunctionType ft 
     _ -> internalError "conLoweredFunctionType: Not a function type"