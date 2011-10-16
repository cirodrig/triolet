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
                    Type.Var.Var -> Maybe ([Val] -> Gen m [Val])
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
      [ (pyonBuiltin The_or, binary_bool PrimOr)
      , (pyonBuiltin The_and, binary_bool PrimAnd)
      , (pyonBuiltin The_AdditiveDict_int_add,
         binary_int (PrimAddZ Signed S32))
      , (pyonBuiltin The_AdditiveDict_int_sub,
         binary_int (PrimSubZ Signed S32))
      , (pyonBuiltin The_MultiplicativeDict_int_mul,
         binary_int (PrimMulZ Signed S32))
      , (pyonBuiltin The_MultiplicativeDict_int_fromInt,
         id_int)
      , (pyonBuiltin The_min_int,
         binary_int (PrimMinZ Signed S32))
      , (pyonBuiltin The_max_int,
         binary_int (PrimMaxZ Signed S32))
      , (pyonBuiltin The_AdditiveDict_float_add,
         binary_float (PrimAddF S32))
      , (pyonBuiltin The_AdditiveDict_float_sub,
         binary_float (PrimSubF S32))
      , (pyonBuiltin The_MultiplicativeDict_float_mul,
         binary_float (PrimMulF S32))
      , (pyonBuiltin The_FloatingDict_float_power,
         binary_float (PrimPowF S32))
      , (pyonBuiltin The_FloatingDict_float_exp,
         unary_float (PrimUnaryF ExpI S32))
      , (pyonBuiltin The_FloatingDict_float_log,
         unary_float (PrimUnaryF LogI S32))
      , (pyonBuiltin The_FloatingDict_float_sqrt,
         unary_float (PrimUnaryF SqrtI S32))
      , (pyonBuiltin The_FloatingDict_float_sin,
         unary_float (PrimUnaryF SinI S32))
      , (pyonBuiltin The_FloatingDict_float_cos,
         unary_float (PrimUnaryF CosI S32))
      , (pyonBuiltin The_FloatingDict_float_tan,
         unary_float (PrimUnaryF TanI S32))
      , (pyonBuiltin The_FloatingDict_float_fromfloat,
         id_float)
      , (pyonBuiltin The_VectorDict_float_scale,
         binary_float (PrimMulF S32))
      , (pyonBuiltin The_VectorDict_float_magnitude,
         id_float)
      , (pyonBuiltin The_VectorDict_float_dot,
         binary_float (PrimMulF S32))
      , (pyonBuiltin The_floor,
         float_to_int Floor)
      , (pyonBuiltin The_zero_ii,
         indexed_int_constant 0)
      , (pyonBuiltin The_one_ii,
         indexed_int_constant 1)
      , (pyonBuiltin The_zero_fii,
         fin_indexed_int_constant 0)
      , (pyonBuiltin The_one_fii,
         fin_indexed_int_constant 1)
      , (pyonBuiltin The_emptyEffTok,
         empty_eff_tok)
      , (pyonBuiltin The_fromEffTok,
         from_eff_tok)
      , (pyonBuiltin The_eqZ_refl,
         proof_object)
      , (pyonBuiltin The_deadRef,
         dead_reference)
      , (pyonBuiltin The_deadBox,
         dead_box)
      , (pyonBuiltin The_deadProof,
         proof_object)
      , (pyonBuiltin The_unsafeMakeCoercion,
         proof_object)
      ]

-- | Create a unary float operation.  Return it as a lambda function, so we
-- can use it as a value.
unary_float op =
  genLambdaOrCall [float_type] [float_type] $ \params -> do
    emitAtom [float_type] $ PrimA op params
  where
    float_type = PrimType (FloatType S32)

binary_float op =
  genLambdaOrCall [float_type, float_type] [float_type] $ \params -> do
    emitAtom [float_type] $ PrimA op params
  where
    float_type = PrimType (FloatType S32)

binary_int op =
  genLambdaOrCall [int_type, int_type] [int_type] $ \params -> do
    emitAtom [int_type] $ PrimA op params  
  where
    int_type = PrimType (IntType Signed S32)


binary_bool op =
  genLambdaOrCall [bool_type, bool_type] [bool_type] $ \params -> do
    emitAtom [bool_type] $ PrimA op params
  where
    bool_type = PrimType BoolType

-- | Round a FP number
float_to_int round_mode =
  genLambdaOrCall [float_type] [int_type] $ \params -> do
    emitAtom [int_type] $ PrimA (PrimRoundF round_mode S32 Signed S32) params
  where
    int_type = PrimType (IntType Signed S32)
    float_type = PrimType (FloatType S32)
  
id_float, id_int, empty_eff_tok, from_eff_tok, dead_reference, dead_box, proof_object ::
  (Monad m, Supplies m (Ident Var)) => [Val] -> Gen m [Val]

-- | This is the identity function on floats.
id_float =
  genLambdaOrCall [float_type] [float_type] return
  where
    float_type = PrimType (FloatType S32)

-- | This is the identity function on ints.
id_int =
  genLambdaOrCall [int_type] [int_type] return
  where
    int_type = PrimType (IntType Signed S32)

indexedIntType = RecordType indexedIntRecord

indexed_int_constant n [] =
  return [RecV indexedIntRecord [uint8V 0,
                                 RecV indexedIntDataRecord [RecV finIndexedIntRecord [nativeIntV n]]]]

fin_indexed_int_constant n [] =
  return [RecV finIndexedIntRecord [nativeIntV n]]

-- | Create an effect token.
empty_eff_tok [] = return [LitV UnitL]

-- | Convert an effect token to a side effect.  The effect token is simply
--   discarded.
from_eff_tok =
  genLambdaOrCall [PrimType UnitType] [] $ \_ -> do
    emitAtom [] $ ValA []

-- | Initialize an object that's dead.  Since it's dead, we don't have to  
--   initialize it.
dead_reference =
  genLambdaOrCall [PrimType PointerType] [] $ \_ -> do
    emitAtom [] $ ValA []

-- | Create a dead boxed object.
dead_box = do
  genLambdaOrCall [PrimType PointerType] [] $ \_ -> do
    emitAtom [] $ ValA []

-- | Create a proof object or coercion value.
proof_object [] = return [LitV UnitL]