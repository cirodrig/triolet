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
                    Type.Var.Var -> Maybe ([Val] -> Gen m Val)
lowerIntrinsicOp v 
    -- Check size assumptions
  | trioletFloatSize /= S32 =
    internalError "lowerIntrinsicOp: Unexpected float size"
  | trioletIntSize /= S32 =
    internalError "lowerIntrinsicOp: Unexpected int size"
  | otherwise = IntMap.lookup (fromIdent $ Type.Var.varID v) table
  where
    table =
      IntMap.fromList [(fromIdent $ Type.Var.varID v, f) | (v, f) <- assocs]

    assocs =
      [ (coreBuiltin The_or, bool_operation PrimOr)
      , (coreBuiltin The_and, bool_operation PrimAnd)
      , (coreBuiltin The_oper_BITWISEAND,
         binary_int (PrimAndZ Signed S32))
      , (coreBuiltin The_oper_BITWISEOR,
         binary_int (PrimOrZ Signed S32))
      , (coreBuiltin The_oper_BITWISEXOR,
         binary_int (PrimXorZ Signed S32))
      , (coreBuiltin The_uintToInt,
         uint_to_int)
      , (coreBuiltin The_intToUint,
         int_to_uint)
      , (coreBuiltin The_lshift,
         binary_int (PrimShiftL Signed S32))
      , (coreBuiltin The_rshift,
         binary_int (PrimShiftR Signed S32))
      , (coreBuiltin The_addI,
         binary_int (PrimAddZ Signed S32))
      , (coreBuiltin The_subI,
         binary_int (PrimSubZ Signed S32))
      , (coreBuiltin The_mulI,
         binary_int (PrimMulZ Signed S32))
      --, (coreBuiltin The_MultiplicativeDict_int_fromInt,
      --   id_int)
      , (coreBuiltin The_minI,
         binary_int (PrimMinZ Signed S32))
      , (coreBuiltin The_maxI,
         binary_int (PrimMaxZ Signed S32))
      , (coreBuiltin The_addU,
         binary_uint (PrimAddZ Unsigned S32))
      , (coreBuiltin The_subU,
         binary_uint (PrimSubZ Unsigned S32))
      , (coreBuiltin The_mulU,
         binary_uint (PrimMulZ Unsigned S32))
      , (coreBuiltin The_minU,
         binary_uint (PrimMinZ Unsigned S32))
      , (coreBuiltin The_maxU,
         binary_uint (PrimMaxZ Unsigned S32))
      , (coreBuiltin The_addF,
         binary_float (PrimAddF S32))
      , (coreBuiltin The_subF,
         binary_float (PrimSubF S32))
      , (coreBuiltin The_mulF,
         binary_float (PrimMulF S32))
      , (coreBuiltin The_powF,
         binary_float (PrimPowF S32))
      , (coreBuiltin The_expF,
         unary_float (PrimUnaryF ExpI S32))
      , (coreBuiltin The_logF,
         unary_float (PrimUnaryF LogI S32))
      , (coreBuiltin The_sqrtF,
         unary_float (PrimUnaryF SqrtI S32))
      , (coreBuiltin The_sinF,
         unary_float (PrimUnaryF SinI S32))
      , (coreBuiltin The_cosF,
         unary_float (PrimUnaryF CosI S32))
      , (coreBuiltin The_tanF,
         unary_float (PrimUnaryF TanI S32))
      --, (coreBuiltin The_FloatingDict_float_fromfloat,
      --   id_float)
      , (coreBuiltin The_VectorDict_float_scale,
         binary_float (PrimMulF S32))
      , (coreBuiltin The_VectorDict_float_magnitude,
         id_float)
      , (coreBuiltin The_VectorDict_float_dot,
         binary_float (PrimMulF S32))
      , (coreBuiltin The_floor,
         float_to_int Floor)
      , (coreBuiltin The_zero_ii,
         indexed_int_constant 0)
      , (coreBuiltin The_one_ii,
         indexed_int_constant 1)
      , (coreBuiltin The_zero_fii,
         fin_indexed_int_constant 0)
      , (coreBuiltin The_one_fii,
         fin_indexed_int_constant 1)
      , (coreBuiltin The_emptyEffTok,
         empty_eff_tok)
      , (coreBuiltin The_deadRef,
         dead_reference)
      , (coreBuiltin The_deadBox,
         dead_box)
      , (coreBuiltin The_unsafeMakeCoercion,
         proof_object)
      {-, (coreBuiltin The_sizealign_int,
         sizealign_int)
      , (coreBuiltin The_sizealign_uint,
         sizealign_uint)
      , (coreBuiltin The_sizealign_float,
         sizealign_float)
      , (coreBuiltin The_sizealign_NoneType,
         sizealign_NoneType)
      , (coreBuiltin The_sizealign_EffTok,
         sizealign_EffTok)
      , (coreBuiltin The_sizealign_Ref,
         sizealign_Ref)
      , (coreBuiltin The_sizealign_StuckRef,
         sizealign_StuckRef)
      , (coreBuiltin The_sizealign_ListBuilder,
         sizealign_ListBuilder)
      , (coreBuiltin The_sizealign_append_list,
         sizealign_append_list)
      , (coreBuiltin The_sizealign_array0,
         sizealign_array0)
      , (coreBuiltin The_sizealign_array1,
         sizealign_array1)
      , (coreBuiltin The_sizealign_array2,
         sizealign_array2)
      , (coreBuiltin The_sizealign_array3,
         sizealign_array3)
      , (coreBuiltin The_sizealign_list,
         sizealign_list)
      , (coreBuiltin The_sizealign_barray1,
         sizealign_barray1)
      , (coreBuiltin The_sizealign_barray2,
         sizealign_barray2)
      , (coreBuiltin The_sizealign_blist,
         sizealign_blist) -}
      ]

-- | Create a unary float operation.  Return it as a lambda function, so we
-- can use it as a value.
unary_float op =
  genLambdaOrCall1 [float_type] float_type $ \params -> do
    emitAtom1 float_type $ PrimA op params
  where
    float_type = PrimType (FloatType S32)

binary_float op =
  genLambdaOrCall1 [float_type, float_type] float_type $ \params -> do
    emitAtom1 float_type $ PrimA op params
  where
    float_type = PrimType (FloatType S32)

binary_int op =
  genLambdaOrCall1 [int_type, int_type] int_type $ \params -> do
    emitAtom1 int_type $ PrimA op params  
  where
    int_type = PrimType (IntType Signed S32)

binary_uint op =
  genLambdaOrCall1 [uint_type, uint_type] uint_type $ \params -> do
    emitAtom1 uint_type $ PrimA op params  
  where
    uint_type = PrimType (IntType Unsigned S32)

-- | Perform a boolean operation.  Convert arguments to/from words.
bool_operation op =
  genLambdaOrCall1 [uint_type, uint_type] uint_type $ \ [x, y] -> do
    b1 <- emitAtom1 bool_type $ PrimA (PrimCmpZ Unsigned S32 CmpNE) [x, zero]
    b2 <- emitAtom1 bool_type $ PrimA (PrimCmpZ Unsigned S32 CmpNE) [y, zero]
    bool_result <- emitAtom1 bool_type $ PrimA op [b1, b2]
    emitAtom1 uint_type $ PrimA (PrimSelect uint_type) [bool_result, one, zero]
  where
    one = LitV (IntL Unsigned S32 1)
    zero = LitV (IntL Unsigned S32 0)
    uint_type = PrimType (IntType Unsigned S32)
    bool_type = PrimType BoolType

-- | Round a FP number
float_to_int round_mode =
  genLambdaOrCall1 [float_type] int_type $ \params -> do
    emitAtom1 int_type $ PrimA (PrimRoundF round_mode S32 Signed S32) params
  where
    int_type = PrimType (IntType Signed S32)
    float_type = PrimType (FloatType S32)
  
-- | Cast unsigned to signed int
uint_to_int =
  genLambdaOrCall1 [uint_type] int_type $ \params -> do
    emitAtom1 int_type $ PrimA (PrimCastZ Unsigned Signed S32) params
  where
    int_type = PrimType (IntType Signed S32)
    uint_type = PrimType (IntType Unsigned S32)

-- | Cast signed to unsigned int
int_to_uint =
  genLambdaOrCall1 [int_type] uint_type $ \params -> do
    emitAtom1 uint_type $ PrimA (PrimCastZ Signed Unsigned S32) params
  where
    int_type = PrimType (IntType Signed S32)
    uint_type = PrimType (IntType Unsigned S32)

id_float, id_int, empty_eff_tok, dead_reference, dead_box, proof_object ::
  (Monad m, Supplies m (Ident Var)) => [Val] -> Gen m Val

-- | This is the identity function on floats.
id_float =
  genLambdaOrCall1 [float_type] float_type (\ [x] -> return x)
  where
    float_type = PrimType (FloatType S32)

-- | This is the identity function on ints.
id_int =
  genLambdaOrCall1 [int_type] int_type (\ [x] -> return x)
  where
    int_type = PrimType (IntType Signed S32)

indexedIntType = RecordType indexedIntRecord

indexed_int_constant n [] =
  return (RecV indexedIntRecord [uint8V 0,
                                 RecV indexedIntDataRecord [RecV finIndexedIntRecord [nativeIntV n]]])

fin_indexed_int_constant n [] =
  return (RecV finIndexedIntRecord [nativeIntV n])

-- | Create an effect token.
empty_eff_tok [] = return (LitV UnitL)

-- | Initialize an object that's dead.  Since it's dead, we don't have to  
--   initialize it.
dead_reference =
  genLambdaOrCall1 [PrimType PointerType] (PrimType UnitType) $ \_ -> return $ LitV UnitL

-- | Create a dead boxed object.
dead_box = do
  genLambdaOrCall1 [PrimType PointerType] (PrimType UnitType) $ \_ -> return $ LitV UnitL

-- | Create a proof object or coercion value.
proof_object [] = return (LitV UnitL)

sizeAlignValue t = RecV sizeAlignRecord [nativeWordV (sizeOf t), nativeWordV (alignOf t)]

-- | Size constants
sizealign_int [] = return [sizeAlignValue trioletIntType]
sizealign_uint [] = return [sizeAlignValue trioletUintType]
sizealign_float [] = return [sizeAlignValue trioletFloatType]
sizealign_NoneType [] = return [sizeAlignValue trioletNoneType]
sizealign_EffTok [] = return [sizeAlignValue UnitType]
sizealign_Ref [] = return [sizeAlignValue ref_record]
  where ref_record = mutableStaticRecord [PrimField OwnedType]
sizealign_StuckRef [] = return [sizeAlignValue ref_record]
  where ref_record = mutableStaticRecord [PrimField OwnedType]

sizealign_ListBuilder [] = return [sizeAlignValue list_builder_type]
  where
    list_builder_type = mutableStaticRecord [PrimField trioletIntType,
                                             PrimField trioletIntType,
                                             PrimField OwnedType]

sizealign_append_list [] = return [sizeAlignValue append_list_type]
  where
    append_list_type = mutableStaticRecord [RecordField finIndexedIntRecord,
                                            PrimField trioletIntType,
                                            PrimField OwnedType]

sizealign_array0 [] = return [sizeAlignValue array0Record]
sizealign_array1 [] = return [sizeAlignValue array1Record]
sizealign_array2 [] = return [sizeAlignValue array2Record]
sizealign_array3 [] = return [sizeAlignValue array3Record]
sizealign_list [] = return [sizeAlignValue listRecord]
sizealign_barray1 [] = return [sizeAlignValue barray1Record]
sizealign_barray2 [] = return [sizeAlignValue barray2Record]
sizealign_barray3 [] = return [sizeAlignValue barray3Record]
sizealign_blist [] = return [sizeAlignValue blistRecord]
