{-| Intrinsic operator lookup.

For functions that translate down to a single instruction, we provide the
equivalent instruction here.
-}

{-# LANGUAGE FlexibleContexts #-}
module LowLevel.Intrinsics(lowerIntrinsicOp)
where

import qualified Data.IntMap as IntMap

import Common.Error
import Common.Identifier
import Common.Supply
import Builtins.Builtins
import LowLevel.Syntax
import LowLevel.Build
import LowLevel.CodeTypes
import LowLevel.Records
import qualified Type.Var

lowerIntrinsicOp :: (Monad m, Supplies m (Ident Var)) =>
                    Type.Var.Var -> Maybe (m Val)
lowerIntrinsicOp v 
    -- Check size assumptions
  | pyonFloatSize /= S32 =
    internalError "lowerIntrinsicOp: Unexpected float size"
  | pyonIntSize /= S32 =
    internalError "lowerIntrinsicOp: Unexpected int size"
  | otherwise = IntMap.lookup (fromIdent $ Type.Var.varID v) table
  where
    table =
      IntMap.fromList [(fromIdent $ Type.Var.varID v, f) | (v, f) <- assocs]

    assocs =
      [ (pyonBuiltin the_or, binary_bool PrimOr)
      , (pyonBuiltin the_and, binary_bool PrimAnd)
      , (pyonBuiltin the_AdditiveDict_int_add,
         binary_int (PrimAddZ Signed S32))
      , (pyonBuiltin the_AdditiveDict_int_sub,
         binary_int (PrimSubZ Signed S32))
      , (pyonBuiltin the_MultiplicativeDict_int_mul,
         binary_int (PrimMulZ Signed S32))
      , (pyonBuiltin the_MultiplicativeDict_int_fromInt,
         id_int)
      , (pyonBuiltin the_AdditiveDict_float_add,
         binary_float (PrimAddF S32))
      , (pyonBuiltin the_AdditiveDict_float_sub,
         binary_float (PrimSubF S32))
      , (pyonBuiltin the_MultiplicativeDict_float_mul,
         binary_float (PrimMulF S32))
      , (pyonBuiltin the_FloatingDict_float_power,
         binary_float (PrimPowF S32))
      , (pyonBuiltin the_FloatingDict_float_exp,
         unary_float (PrimUnaryF ExpI S32))
      , (pyonBuiltin the_FloatingDict_float_log,
         unary_float (PrimUnaryF LogI S32))
      , (pyonBuiltin the_FloatingDict_float_sqrt,
         unary_float (PrimUnaryF SqrtI S32))
      , (pyonBuiltin the_FloatingDict_float_sin,
         unary_float (PrimUnaryF SinI S32))
      , (pyonBuiltin the_FloatingDict_float_cos,
         unary_float (PrimUnaryF CosI S32))
      , (pyonBuiltin the_FloatingDict_float_tan,
         unary_float (PrimUnaryF TanI S32))
      , (pyonBuiltin the_FloatingDict_float_fromfloat,
         id_float)
      , (pyonBuiltin the_VectorDict_float_scale,
         binary_float (PrimMulF S32))
      , (pyonBuiltin the_VectorDict_float_magnitude,
         id_float)
      , (pyonBuiltin the_VectorDict_float_dot,
         binary_float (PrimMulF S32))
      , (pyonBuiltin the_floor,
         float_to_int Floor)
      , (pyonBuiltin the_zero_ii,
         indexed_int_constant 0)
      , (pyonBuiltin the_one_ii,
         indexed_int_constant 1)
      , (pyonBuiltin the_emptyEffTok,
         empty_eff_tok)
      , (pyonBuiltin the_eqZ_refl,
         proof_object)
      , (pyonBuiltin the_deadProof,
         proof_object)
      ]

-- | Create a unary float operation.  Return it as a lambda function, so we
-- can use it as a value.
unary_float op = do
  let float_type = PrimType (FloatType S32)
  param_var <- newAnonymousVar float_type
  let atom = PrimA op [VarV param_var]
  return $ LamV $ closureFun [param_var] [float_type] $ ReturnE atom

binary_float op = do
  let float_type = PrimType (FloatType S32)
  param_var1 <- newAnonymousVar float_type
  param_var2 <- newAnonymousVar float_type
  let atom = PrimA op [VarV param_var1, VarV param_var2]
  return $ LamV $ closureFun [param_var1, param_var2] [float_type] $ ReturnE atom

binary_int op = do
  let int_type = PrimType (IntType Signed S32)
  param_var1 <- newAnonymousVar int_type
  param_var2 <- newAnonymousVar int_type
  let atom = PrimA op [VarV param_var1, VarV param_var2]
  return $ LamV $ closureFun [param_var1, param_var2] [int_type] $ ReturnE atom

binary_bool op = do
  let bool_type = PrimType BoolType
  param_var1 <- newAnonymousVar bool_type
  param_var2 <- newAnonymousVar bool_type
  let atom = PrimA op [VarV param_var1, VarV param_var2]
  return $ LamV $ closureFun [param_var1, param_var2] [bool_type] $ ReturnE atom

-- | Round a FP number
float_to_int round_mode = do
  let int_type = PrimType (IntType Signed S32)
  let float_type = PrimType (FloatType S32)
  param_var <- newAnonymousVar float_type
  let atom = PrimA (PrimRoundF round_mode S32 Signed S32) [VarV param_var]
  return $ LamV $ closureFun [param_var] [int_type] $ ReturnE atom
  
-- | This is the identity function on floats.
id_float :: (Monad m, Supplies m (Ident Var)) => m Val
id_float = do
  let float_type = PrimType (FloatType S32)
  param_var <- newAnonymousVar float_type
  let atom = ValA [VarV param_var]
  return $ LamV $ closureFun [param_var] [float_type] $ ReturnE atom

-- | This is the identity function on ints.
id_int :: (Monad m, Supplies m (Ident Var)) => m Val
id_int = do
  let int_type = PrimType (IntType Signed S32)
  param_var <- newAnonymousVar int_type
  let atom = ValA [VarV param_var]
  return $ LamV $ closureFun [param_var] [int_type] $ ReturnE atom

indexedIntType = RecordType indexedIntRecord

indexed_int_constant :: (Monad m, Supplies m (Ident Var)) => Integer -> m Val
indexed_int_constant n =
  return $ RecV indexedIntRecord [uint8V 0,
                                  RecV indexedIntDataRecord [nativeIntV n]]

-- | Create an effect token.
empty_eff_tok :: (Monad m, Supplies m (Ident Var)) => m Val
empty_eff_tok = return (LitV UnitL)

-- | Create a proof object.
proof_object :: (Monad m, Supplies m (Ident Var)) => m Val
proof_object = return (LitV UnitL)