{-| Definitions of Core types of builtin constructors.
-}
module Core.BuiltinTypes(dumpCoreTypes, conCoreType, conCoreReturnType)
where

import qualified Data.IntMap as IntMap
import Text.PrettyPrint.HughesPJ
import System.IO.Unsafe

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Core
import qualified Gluon.Core.Builtins.Effect
import Gluon.Eval.Environment
import Gluon.Eval.Eval
import SystemF.Builtins
import Core.Syntax
import Core.Gluon
import Core.Print

-- | Format the table of types as a string for human reading.
dumpCoreTypes :: () -> String
dumpCoreTypes () =
  show $ vcat $ map dump_type_sig $ IntMap.toList constructorTable
  where
    dump_type_sig (id, val) =
      text ("#" ++ show id) $$ nest 4 (pprReturnT val)

-- | Get the core return type of a constructor.  This is the type returned by
-- a 'ValueConV' or 'OwnedConV' expression.
conCoreReturnType :: Con -> CBind CReturnT Rec
conCoreReturnType c =
  case IntMap.lookup (fromIdent $ conID c) constructorTable
  of Just ty -> ty
     Nothing ->
       internalError $ "conCoreReturnType: No information for constructor " ++ showLabel (conName c)

-- | Get the core type of a constructor.
conCoreType :: Con -> RCType
conCoreType c = cbindType $ conCoreReturnType c

-------------------------------------------------------------------------------

emptyEffectType :: RCType
emptyEffectType = expCT Gluon.Core.Builtins.Effect.empty

-- | Create the effect of reading the given address and type.
readEffectType :: RExp -> RCType -> RCType
readEffectType addr ty =
  let at = mkInternalConE $ builtin the_AtE
  in appExpCT at [ty, expCT addr]

unionEffect :: RCType -> RCType -> RCType
unionEffect t1 t2 =
  let sconj = mkInternalConE $ builtin the_SconjE 
  in appExpCT sconj [t1, t2]

unionEffects :: [RCType] -> RCType
unionEffects [] = emptyEffectType
unionEffects es = foldr1 unionEffect es

addressType :: RExp
addressType = mkInternalConE $ builtin the_Addr

-- | Run the computation to construct a function type.
--
-- The resulting expression will use the same variable IDs as other
-- expressions.  However, since it's a closed expression and the IDs will be  
-- freshened before use, this is fine.
mkConType :: Eval (CBind CReturnT Rec) -> CBind CReturnT Rec
mkConType m = unsafePerformIO $ do
  val_supply <- newIdentSupply
  result <- runEvalIO val_supply m
  case result of Just x -> return x
                 Nothing -> internalError "mkConType"

passConvOf :: RCType -> RCType
passConvOf a = appCT (conCT $ pyonBuiltin the_PassConv) [a]

mkValBinaryOpType :: RExp -> CBind CReturnT Rec
mkValBinaryOpType ty =
  let constructor_type =
        funCT $
        pureArrCT (ValPT Nothing ::: expCT ty) $
        pureArrCT (ValPT Nothing ::: expCT ty) $
        retCT (ValRT ::: expCT ty)
  in OwnRT ::: constructor_type

mkValUnaryOpType :: RExp -> CBind CReturnT Rec
mkValUnaryOpType ty =
  let constructor_type =
        funCT $
        pureArrCT (ValPT Nothing ::: expCT ty) $
        retCT (ValRT ::: expCT ty)
  in OwnRT ::: constructor_type

mkRefBinaryOpType :: RExp -> Eval (CBind CReturnT Rec)
mkRefBinaryOpType ty = do
  addr1 <- newAnonymousVariable ObjectLevel
  addr2 <- newAnonymousVariable ObjectLevel
  let constructor_type =
        funCT $
        pureArrCT (ReadPT addr1 ::: expCT ty) $
        pureArrCT (ReadPT addr2 ::: expCT ty) $
        retCT (WriteRT ::: expCT ty)
  return $ OwnRT ::: constructor_type

mkRefUnaryOpType :: RExp -> Eval (CBind CReturnT Rec)
mkRefUnaryOpType ty = do
  addr1 <- newAnonymousVariable ObjectLevel
  let constructor_type =
        funCT $
        pureArrCT (ReadPT addr1 ::: expCT ty) $
        retCT (WriteRT ::: expCT ty)
  return $ OwnRT ::: constructor_type

binaryIntOpType = mkValBinaryOpType $ mkInternalConE $ pyonBuiltin the_int
binaryFloatOpType = mkValBinaryOpType $ mkInternalConE $ pyonBuiltin the_float

unaryIntOpType = mkValUnaryOpType $ mkInternalConE $ pyonBuiltin the_int
unaryFloatOpType = mkValUnaryOpType $ mkInternalConE $ pyonBuiltin the_float

mkValZeroOpType ty = ValRT ::: expCT ty

mkRefZeroOpType ty = do
  addr <- newAnonymousVariable ObjectLevel
  let constructor_type =
        funCT $
        pureArrCT (ReadPT addr ::: conCT (pyonBuiltin the_NoneType)) $
        retCT (WriteRT ::: expCT ty)
  return $ OwnRT ::: constructor_type

valueIntOpType = mkValZeroOpType $ mkInternalConE $ pyonBuiltin the_int
valueFloatOpType = mkValZeroOpType $ mkInternalConE $ pyonBuiltin the_float

valFromIntType ty =
  let constructor_type =
        funCT $
        pureArrCT (ValPT Nothing ::: conCT (pyonBuiltin the_int)) $
        retCT ty
  in OwnRT ::: constructor_type

mkCompareOpType :: RExp -> CBind CReturnT Rec
mkCompareOpType ty =
  let con_type =
        funCT $
        pureArrCT (ValPT Nothing ::: expCT ty) $
        pureArrCT (ValPT Nothing ::: expCT ty) $
        retCT (ValRT ::: conCT (pyonBuiltin the_bool))
  in OwnRT ::: con_type

compareIntOpType = mkCompareOpType $ mkInternalConE $ pyonBuiltin the_int
compareFloatOpType = mkCompareOpType $ mkInternalConE $ pyonBuiltin the_float

loadType t = mkConType $ do
  a <- newAnonymousVariable ObjectLevel
  let constructor_type =
        funCT $
        pureArrCT (ReadPT a ::: t) $
        retCT (ValRT ::: t)
  return (OwnRT ::: constructor_type)

storeType t = mkConType $ do
  let constructor_type =
        funCT $
        pureArrCT (ValPT Nothing ::: t) $
        retCT (WriteRT ::: t)
  return (OwnRT ::: constructor_type)

loadIntType = loadType $ expCT (mkInternalConE $ pyonBuiltin the_int)
storeIntType = storeType $ expCT (mkInternalConE $ pyonBuiltin the_int)
loadFloatType = loadType $ expCT (mkInternalConE $ pyonBuiltin the_float)
storeFloatType = storeType $ expCT (mkInternalConE $ pyonBuiltin the_float)
loadBoolType = loadType $ expCT (mkInternalConE $ pyonBuiltin the_bool)
storeBoolType = storeType $ expCT (mkInternalConE $ pyonBuiltin the_bool)
loadNoneTypeType = loadType $ expCT (mkInternalConE $ pyonBuiltin the_NoneType)
storeNoneTypeType = storeType $ expCT (mkInternalConE $ pyonBuiltin the_NoneType)
      
subscriptType = mkConType $ do
  a <- newAnonymousVariable TypeLevel
  pc_addr <- newAnonymousVariable ObjectLevel
  base_addr <- newAnonymousVariable ObjectLevel
  let constructor_type =
        funCT $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ReadPT pc_addr ::: passConvOf (varCT a)) $
        pureArrCT (ReadPT base_addr ::: varCT a) $
        pureArrCT (ValPT Nothing ::: conCT (pyonBuiltin the_int)) $
        retCT (ReadRT (mkInternalVarE $ pyonBuiltin the_dummy_addr) ::: varCT a)
  return (OwnRT ::: constructor_type)

additiveDictType = mkConType $ do
  a <- newAnonymousVariable TypeLevel
  pc_addr <- newAnonymousVariable ObjectLevel
  binary_type <- mkRefBinaryOpType (mkInternalVarE a)
  unary_type <- mkRefUnaryOpType (mkInternalVarE a)
  zero_addr <- newAnonymousVariable ObjectLevel
  let constructor_type =
        funCT $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ReadPT pc_addr ::: passConvOf (varCT a)) $
        pureArrCT (OwnPT ::: cbindType binary_type) $
        pureArrCT (OwnPT ::: cbindType binary_type) $
        pureArrCT (OwnPT ::: cbindType unary_type) $
        pureArrCT (ReadPT zero_addr ::: varCT a) $
        retCT (WriteRT ::: appExpCT (mkInternalConE $ pyonBuiltin the_AdditiveDict) [varCT a])
  return (OwnRT ::: constructor_type)

-- | Additive dictionary constructor for type 'complex'
additiveDictComplexType = mkConType $ do
  a <- newAnonymousVariable TypeLevel
  dict_addr <- newAnonymousVariable ObjectLevel
  let additive_dict a =
        appExpCT (mkInternalConE $ pyonBuiltin the_AdditiveDict) [a]
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ReadPT (dict_addr) ::: additive_dict (varCT a)) $
        retCT (WriteRT ::: additive_dict (appExpCT (mkInternalConE $ pyonBuiltin the_complex) [varCT a]))
  return (OwnRT ::: constructor_type)

multiplicativeDictType = mkConType $ do
  a <- newAnonymousVariable TypeLevel
  additive_addr <- newAnonymousVariable ObjectLevel
  binary_type <- mkRefBinaryOpType (mkInternalVarE a)
  one_addr <- newAnonymousVariable ObjectLevel
  let from_int_type =
        funCT $
        pureArrCT (ValPT Nothing ::: conCT (pyonBuiltin the_int)) $
        retCT (WriteRT ::: varCT a)
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ReadPT additive_addr ::: appCT (conCT $ pyonBuiltin the_AdditiveDict) [varCT a]) $
        pureArrCT (OwnPT ::: cbindType binary_type) $
        pureArrCT (OwnPT ::: from_int_type) $
        pureArrCT (ReadPT one_addr ::: varCT a) $
        retCT (WriteRT ::: appExpCT (mkInternalConE $ pyonBuiltin the_MultiplicativeDict) [varCT a])
  return (OwnRT ::: constructor_type)

traversableDictType = mkConType $ do
  t <- newAnonymousVariable TypeLevel
  traverse_type <- mkTraverseType (varCT t)
  build_type <- mkBuildType (varCT t)
  let dict_type =
        appExpCT (mkInternalConE $ pyonBuiltin the_TraversableDict) [varCT t]
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just t) ::: expCT (mkInternalArrowE False pureKindE pureKindE)) $
        pureArrCT (OwnPT ::: cbindType traverse_type) $
        pureArrCT (OwnPT ::: cbindType build_type) $
        retCT (WriteRT ::: dict_type)
  return (OwnRT ::: constructor_type)

copyType = mkConType $ do
  a <- newAnonymousVariable TypeLevel
  addr1 <- newAnonymousVariable ObjectLevel
  addr2 <- newAnonymousVariable ObjectLevel
  let pc_type = passConvOf (varCT a)
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ReadPT addr1 ::: pc_type) $
        pureArrCT (ReadPT addr2 ::: varCT a) $
        retCT (WriteRT ::: varCT a)
  return (OwnRT ::: constructor_type)

mkBuildType t = do
  e <- newAnonymousVariable TypeLevel
  a <- newAnonymousVariable TypeLevel
  addr <- newAnonymousVariable ObjectLevel
  let pc_type = passConvOf (varCT a)
      stream_type = appCT (conCT $ pyonBuiltin the_LazyStream)
                    [varCT e, varCT a]
      list_type = appCT t [varCT a]
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just e) ::: expCT effectKindE) $ 
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ReadPT addr ::: pc_type) $
        arrCT (OwnPT ::: stream_type) (varCT e) $
        retCT (WriteRT ::: list_type)
  return (OwnRT ::: constructor_type)

streamBindType = mkConType $ do
  e <- newAnonymousVariable TypeLevel
  a <- newAnonymousVariable TypeLevel
  b <- newAnonymousVariable TypeLevel
  addr <- newAnonymousVariable ObjectLevel
  addr_pc_a <- newAnonymousVariable ObjectLevel
  addr_pc_b <- newAnonymousVariable ObjectLevel
  let pc_a_type = passConvOf (varCT a)
      pc_b_type = passConvOf (varCT b)
      producer_type = appCT (conCT $ pyonBuiltin the_LazyStream)
                    [varCT e, varCT a]
      result_type = appCT (conCT $ pyonBuiltin the_LazyStream)
                    [varCT e, varCT b]
      consumer_stream_type =
        appCT (conCT $ pyonBuiltin the_LazyStream)
        [ readEffectType (mkInternalVarE addr) (varCT a) `unionEffect` varCT e
        , varCT b]
      consumer_type = 
        funCT $
        arrCT (ReadPT addr ::: varCT a) (varCT e) $
        retCT (OwnRT ::: consumer_stream_type)
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just e) ::: expCT effectKindE) $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ValPT (Just b) ::: expCT pureKindE) $
        pureArrCT (ReadPT addr_pc_a ::: pc_a_type) $
        pureArrCT (ReadPT addr_pc_b ::: pc_b_type) $
        pureArrCT (OwnPT ::: producer_type) $
        pureArrCT (OwnPT ::: consumer_type) $
        retCT (OwnRT ::: result_type)
  return (OwnRT ::: constructor_type)

mkTraverseType t = do
  a <- newAnonymousVariable TypeLevel
  addr <- newAnonymousVariable ObjectLevel
  addr_pc <- newAnonymousVariable ObjectLevel
  let pc_type = passConvOf (varCT a)
      list_type = appCT t [varCT a]
      stream_type = appCT (conCT $ pyonBuiltin the_LazyStream)
                    [readEffectType (mkInternalVarE addr) list_type, varCT a]
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ReadPT addr_pc ::: pc_type) $
        pureArrCT (ReadPT addr ::: list_type) $
        retCT (OwnRT ::: stream_type)
  return (OwnRT ::: constructor_type)

streamIdType = mkConType $ do
  a <- newAnonymousVariable TypeLevel
  e <- newAnonymousVariable TypeLevel
  addr_pc <- newAnonymousVariable ObjectLevel
  let pc_type = passConvOf (varCT a)
      stream_type = appCT (conCT $ pyonBuiltin the_LazyStream)
                    [varCT e, varCT a]
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just e) ::: expCT effectKindE) $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ReadPT addr_pc ::: pc_type) $
        pureArrCT (OwnPT ::: stream_type) $
        retCT (OwnRT ::: stream_type)
  return (OwnRT ::: constructor_type)
        
streamMapType = mkConType $ do
  e <- newAnonymousVariable TypeLevel
  a <- newAnonymousVariable TypeLevel
  b <- newAnonymousVariable TypeLevel
  addr_pc_a <- newAnonymousVariable ObjectLevel
  addr_pc_b <- newAnonymousVariable ObjectLevel
  addr_arg <- newAnonymousVariable ObjectLevel
  let stream_type = appCT (conCT $ pyonBuiltin the_LazyStream)
                    [varCT e, varCT a]
      result_type = appCT (conCT $ pyonBuiltin the_LazyStream)
                    [varCT e, varCT b]
      transformer_type = 
        funCT $
        arrCT (ReadPT addr_arg ::: varCT a) (varCT e) $ 
        retCT (WriteRT ::: varCT b)
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just e) ::: expCT effectKindE) $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ValPT (Just b) ::: expCT pureKindE) $
        pureArrCT (ReadPT addr_pc_a ::: passConvOf (varCT a)) $
        pureArrCT (ReadPT addr_pc_b ::: passConvOf (varCT b)) $
        pureArrCT (OwnPT ::: transformer_type) $
        pureArrCT (OwnPT ::: stream_type) $
        retCT (OwnRT ::: result_type)
  return (OwnRT ::: constructor_type)

streamReturnType = mkConType $ do
  e <- newAnonymousVariable TypeLevel
  a <- newAnonymousVariable TypeLevel
  addr_pc <- newAnonymousVariable ObjectLevel
  let pc_type = passConvOf (varCT a)
      producer_type =
        funCT $
        arrCT (ValPT Nothing ::: conCT (pyonBuiltin the_NoneType)) (varCT e) $
        retCT (WriteRT ::: varCT a)
      result_type = appCT (conCT $ pyonBuiltin the_LazyStream)
                    [varCT e, varCT a]
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just e) ::: expCT effectKindE) $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ReadPT addr_pc ::: pc_type) $
        pureArrCT (OwnPT ::: producer_type) $
        retCT (OwnRT ::: result_type)
  return (OwnRT ::: constructor_type)

streamGenerateType = mkConType $ do
  e <- newAnonymousVariable TypeLevel
  a <- newAnonymousVariable TypeLevel
  addr_pc <- newAnonymousVariable ObjectLevel
  let pc_type = passConvOf (varCT a)
      producer_type =
        funCT $
        arrCT (ValPT Nothing ::: conCT (pyonBuiltin the_int)) (varCT e) $
        retCT (WriteRT ::: varCT a)
      result_type = appCT (conCT $ pyonBuiltin the_LazyStream)
                    [varCT e, varCT a]
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just e) ::: expCT effectKindE) $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ReadPT addr_pc ::: pc_type) $
        pureArrCT (ValPT Nothing ::: conCT (pyonBuiltin the_int)) $
        pureArrCT (OwnPT ::: producer_type) $
        retCT (OwnRT ::: result_type)
  return (OwnRT ::: constructor_type)

listGenerateType = mkConType $ do
  e <- newAnonymousVariable TypeLevel
  a <- newAnonymousVariable TypeLevel
  addr_pc <- newAnonymousVariable ObjectLevel
  let pc_type = passConvOf (varCT a)
      producer_type =
        funCT $
        arrCT (ValPT Nothing ::: conCT (pyonBuiltin the_int)) (varCT e) $
        retCT (WriteRT ::: varCT a)
      result_type = appCT (conCT $ pyonBuiltin the_list) [varCT a]
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just e) ::: expCT effectKindE) $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ReadPT addr_pc ::: pc_type) $
        pureArrCT (ValPT Nothing ::: conCT (pyonBuiltin the_int)) $
        arrCT (OwnPT ::: producer_type) (varCT e) $
        retCT (WriteRT ::: result_type)
  return (OwnRT ::: constructor_type)

passConvOwnedType = mkConType $ do
  a <- newAnonymousVariable TypeLevel
  let result_type = passConvOf (varCT a)
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        retCT (WriteRT ::: result_type)
  return (OwnRT ::: constructor_type)

passConvIterType = mkConType $ do
  a <- newAnonymousVariable TypeLevel
  addr1 <- newAnonymousVariable ObjectLevel
  let -- Since this is a dictionary parameter, effect types are empty
      stream_type =
        appCT (conCT $ pyonBuiltin the_LazyStream)
        [emptyEffectType, varCT a]
      element_passconv_type = passConvOf (varCT a)
      result_type = passConvOf stream_type
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ReadPT addr1 ::: element_passconv_type) $
        retCT (WriteRT ::: result_type)
  return (OwnRT ::: constructor_type)

passConvListType = mkConType $ do
  a <- newAnonymousVariable TypeLevel
  addr1 <- newAnonymousVariable ObjectLevel
  let list_type =
        appCT (conCT $ pyonBuiltin the_list) [varCT a]
      element_passconv_type = passConvOf (varCT a)
      result_type = passConvOf list_type
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ReadPT addr1 ::: element_passconv_type) $
        retCT (WriteRT ::: result_type)
  return (OwnRT ::: constructor_type)

makeComplexType = mkConType $ do
  let result_type =
        appCT (conCT $ pyonBuiltin the_complex) [conCT $ pyonBuiltin the_float]
      constructor_type =
        funCT $
        pureArrCT (ValPT Nothing ::: conCT (pyonBuiltin the_float)) $
        pureArrCT (ValPT Nothing ::: conCT (pyonBuiltin the_float)) $
        retCT (WriteRT ::: result_type)
  return (OwnRT ::: constructor_type)

tuplePassConvType 2 = mkConType $ do
  a <- newAnonymousVariable TypeLevel
  pc_addr_a <- newAnonymousVariable ObjectLevel
  b <- newAnonymousVariable TypeLevel
  pc_addr_b <- newAnonymousVariable ObjectLevel
  let tuple_con = getPyonTupleType' 2
      tuple_type = appCT (conCT tuple_con) [varCT a, varCT b]
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ValPT (Just b) ::: expCT pureKindE) $
        pureArrCT (ReadPT pc_addr_a ::: passConvOf (varCT a)) $
        pureArrCT (ReadPT pc_addr_b ::: passConvOf (varCT b)) $
        retCT (WriteRT ::: passConvOf tuple_type)
  return (OwnRT ::: constructor_type)

tupleConType 2 = mkConType $ do
  a <- newAnonymousVariable TypeLevel
  pc_addr_a <- newAnonymousVariable ObjectLevel
  addra <- newAnonymousVariable ObjectLevel
  b <- newAnonymousVariable TypeLevel
  pc_addr_b <- newAnonymousVariable ObjectLevel
  addrb <- newAnonymousVariable ObjectLevel
  let tuple_con = getPyonTupleType' 2
      tuple_type = appCT (conCT tuple_con) [varCT a, varCT b]
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ValPT (Just b) ::: expCT pureKindE) $
        pureArrCT (ReadPT pc_addr_a ::: passConvOf (varCT a)) $
        pureArrCT (ReadPT pc_addr_b ::: passConvOf (varCT b)) $
        pureArrCT (ReadPT a ::: varCT a) $
        pureArrCT (ReadPT b ::: varCT b) $
        retCT (WriteRT ::: tuple_type)
  return (OwnRT ::: constructor_type)

constructorTable =
  IntMap.fromList [(fromIdent $ conID c, ty) | (c, ty) <- table]
  where
    table = [ (pyonBuiltin the_passConv_int,
               ReadRT (mkInternalVarE $ pyonBuiltin the_passConv_int_addr) ::: passConvOf (conCT $ pyonBuiltin the_int))
            , (pyonBuiltin the_passConv_float,
               ReadRT (mkInternalVarE $ pyonBuiltin the_passConv_float_addr) ::: passConvOf (conCT $ pyonBuiltin the_float))
            , (pyonBuiltin the_OpaqueTraversableDict_list,
               ReadRT (mkInternalVarE $ pyonBuiltin the_OpaqueTraversableDict_list_addr) ::: appCT (conCT $ pyonBuiltin the_TraversableDict) [conCT $ pyonBuiltin the_list])
            , (pyonBuiltin the_passConv_owned,
               passConvOwnedType)
            , (pyonBuiltin the_passConv_iter,
               passConvIterType)
            , (pyonBuiltin the_passConv_list,
               passConvListType)
            , (getPyonTuplePassConv' 2,
               tuplePassConvType 2)
            , (pyonBuiltin the_makeComplex,
               makeComplexType)
            , (pyonBuiltin SystemF.Builtins.the_fun_store_int,
               storeIntType)
            , (pyonBuiltin SystemF.Builtins.the_fun_load_int,
               loadIntType)
            , (pyonBuiltin SystemF.Builtins.the_fun_store_float,
               storeFloatType)
            , (pyonBuiltin SystemF.Builtins.the_fun_load_float,
               loadFloatType)
            , (pyonBuiltin SystemF.Builtins.the_fun_store_bool,
               storeBoolType)
            , (pyonBuiltin SystemF.Builtins.the_fun_load_bool,
               loadBoolType)
            , (pyonBuiltin SystemF.Builtins.the_fun_store_NoneType,
               storeNoneTypeType)
            , (pyonBuiltin SystemF.Builtins.the_fun_load_NoneType,
               loadNoneTypeType)
            , (pyonBuiltin (eqMember . the_EqDict_int),
               compareIntOpType)
            , (pyonBuiltin (neMember . the_EqDict_int),
               compareIntOpType)
            , (pyonBuiltin (eqMember . the_EqDict_float),
               compareFloatOpType)
            , (pyonBuiltin (neMember . the_EqDict_float),
               compareFloatOpType)
            , (pyonBuiltin (ltMember . the_OrdDict_int),
               compareIntOpType)
            , (pyonBuiltin (gtMember . the_OrdDict_int),
               compareIntOpType)
            , (pyonBuiltin (leMember . the_OrdDict_int),
               compareIntOpType)
            , (pyonBuiltin (geMember . the_OrdDict_int),
               compareIntOpType)
            , (pyonBuiltin (ltMember . the_OrdDict_float),
               compareFloatOpType)
            , (pyonBuiltin (gtMember . the_OrdDict_float),
               compareFloatOpType)
            , (pyonBuiltin (leMember . the_OrdDict_float),
               compareFloatOpType)
            , (pyonBuiltin (geMember . the_OrdDict_float),
               compareFloatOpType)
            , (pyonBuiltin (addMember . the_AdditiveDict_int),
               binaryIntOpType)
            , (pyonBuiltin (subMember . the_AdditiveDict_int),
               binaryIntOpType)
            , (pyonBuiltin (negateMember . the_AdditiveDict_int),
               unaryIntOpType)
            , (pyonBuiltin (zeroMember . the_AdditiveDict_int),
               valueIntOpType)
            , (pyonBuiltin (addMember . the_AdditiveDict_float),
               binaryFloatOpType)
            , (pyonBuiltin (subMember . the_AdditiveDict_float),
               binaryFloatOpType)
            , (pyonBuiltin (negateMember . the_AdditiveDict_float),
               unaryFloatOpType)
            , (pyonBuiltin (zeroMember . the_AdditiveDict_float),
               valueFloatOpType)
            , (pyonBuiltin (mulMember . the_MultiplicativeDict_int),
               binaryIntOpType)
            , (pyonBuiltin (fromIntMember . the_MultiplicativeDict_int),
               valFromIntType (ValRT ::: conCT (pyonBuiltin the_int)))
            , (pyonBuiltin (oneMember . the_MultiplicativeDict_int),
               valueIntOpType)
            , (pyonBuiltin (mulMember . the_MultiplicativeDict_float),
               binaryFloatOpType)
            , (pyonBuiltin (fromIntMember . the_MultiplicativeDict_float),
               valFromIntType (ValRT ::: conCT (pyonBuiltin the_float)))
            , (pyonBuiltin (oneMember . the_MultiplicativeDict_float),
               valueFloatOpType)
            , (pyonBuiltin the_fun_subscript,
               subscriptType)
            , (pyonBuiltin (traverseMember . the_TraversableDict_list),
               mkConType $ mkTraverseType (conCT $ pyonBuiltin the_list))
            , (pyonBuiltin (buildMember . the_TraversableDict_list),
               mkConType $ mkBuildType (conCT $ pyonBuiltin the_list))
            , (pyonBuiltin (traverseMember . the_TraversableDict_Stream),
               streamIdType)
            , (pyonBuiltin (buildMember . the_TraversableDict_Stream),
               streamIdType)
            , (pyonBuiltin the_additiveDict,
               additiveDictType)
            , (pyonBuiltin the_multiplicativeDict,
               multiplicativeDictType)
            , (pyonBuiltin the_traversableDict,
               traversableDictType)
            , (getPyonTupleCon' 2,
               tupleConType 2)
            , (pyonBuiltin the_additiveDict_complex,
               additiveDictComplexType)
            , (pyonBuiltin SystemF.Builtins.the_fun_copy,
               copyType)
            , (pyonBuiltin SystemF.Builtins.the_oper_CAT_MAP,
               streamBindType)
            , (pyonBuiltin SystemF.Builtins.the_fun_map_Stream,
               streamMapType)
            , (pyonBuiltin SystemF.Builtins.the_fun_return,
               streamReturnType)
            , (pyonBuiltin SystemF.Builtins.the_fun_generate,
               streamGenerateType)
            , (pyonBuiltin SystemF.Builtins.the_fun_generateList,
               listGenerateType)
            ]
