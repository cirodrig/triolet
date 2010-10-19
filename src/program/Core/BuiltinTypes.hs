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

mkValBinaryOpType :: RExp -> CBind CReturnT Rec
mkValBinaryOpType ty =
  let constructor_type =
        funCT $
        pureArrCT (ValPT Nothing ::: expCT ty) $
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

binaryIntOpType = mkValBinaryOpType $ mkInternalConE $ pyonBuiltin the_int
binaryFloatOpType = mkValBinaryOpType $ mkInternalConE $ pyonBuiltin the_float

mkValZeroOpType ty =
  let constructor_type =
        funCT $
        pureArrCT (ValPT Nothing ::: conCT (pyonBuiltin the_NoneType)) $
        retCT (ValRT ::: expCT ty)
  in OwnRT ::: constructor_type

mkRefZeroOpType ty = do
  addr <- newAnonymousVariable ObjectLevel
  let constructor_type =
        funCT $
        pureArrCT (ReadPT addr ::: conCT (pyonBuiltin the_NoneType)) $
        retCT (WriteRT ::: expCT ty)
  return $ OwnRT ::: constructor_type

zeroIntOpType = mkValZeroOpType $ mkInternalConE $ pyonBuiltin the_int
zeroFloatOpType = mkValZeroOpType $ mkInternalConE $ pyonBuiltin the_float

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

tuple2ConType :: CBind CReturnT Rec
tuple2ConType = mkConType $ do
  a <- newAnonymousVariable TypeLevel
  b <- newAnonymousVariable TypeLevel
  addr1 <- newAnonymousVariable ObjectLevel
  addr2 <- newAnonymousVariable ObjectLevel
  
  let tuple_type =
        appExpCT (mkInternalConE $ getPyonTupleType' 2) [varCT a, varCT b]
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ValPT (Just b) ::: expCT pureKindE) $
        pureArrCT (ReadPT addr1 ::: varCT a) $
        pureArrCT (ReadPT addr2 ::: varCT b) $
        retCT (WriteRT ::: tuple_type)
  return (OwnRT ::: constructor_type)

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
      
additiveDictType = mkConType $ do
  a <- newAnonymousVariable TypeLevel
  binary_type <- mkRefBinaryOpType (mkInternalVarE a)
  zero_type <- mkRefZeroOpType (mkInternalVarE a)
  let constructor_type =
        funCT $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (OwnPT ::: cbindType zero_type) $
        pureArrCT (OwnPT ::: cbindType binary_type) $
        pureArrCT (OwnPT ::: cbindType binary_type) $
        retCT (WriteRT ::: appExpCT (mkInternalConE $ pyonBuiltin the_AdditiveDict) [varCT a])
  return (OwnRT ::: constructor_type)

copyType = mkConType $ do
  a <- newAnonymousVariable TypeLevel
  addr1 <- newAnonymousVariable ObjectLevel
  addr2 <- newAnonymousVariable ObjectLevel
  let pc_type = appCT (conCT $ pyonBuiltin the_PassConv) [varCT a] 
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ReadPT addr1 ::: pc_type) $
        pureArrCT (ReadPT addr2 ::: varCT a) $
        retCT (WriteRT ::: varCT a)
  return (OwnRT ::: constructor_type)

makelistType = mkConType $ do
  e <- newAnonymousVariable TypeLevel
  a <- newAnonymousVariable TypeLevel
  addr <- newAnonymousVariable ObjectLevel
  let pc_type = appCT (conCT $ pyonBuiltin the_PassConv) [varCT a]
      stream_type = appCT (conCT $ pyonBuiltin the_LazyStream)
                    [varCT e, varCT a]
      list_type = appCT (conCT $ pyonBuiltin the_list) [varCT a]
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
  let pc_a_type = appCT (conCT $ pyonBuiltin the_PassConv) [varCT a]
      pc_b_type = appCT (conCT $ pyonBuiltin the_PassConv) [varCT b]
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

listTraverseType = mkConType $ do
  a <- newAnonymousVariable TypeLevel
  addr <- newAnonymousVariable ObjectLevel
  addr_pc <- newAnonymousVariable ObjectLevel
  let pc_type = appCT (conCT $ pyonBuiltin the_PassConv) [varCT a]
      list_type = appCT (conCT $ pyonBuiltin the_list) [varCT a]
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
  let pc_type = appCT (conCT $ pyonBuiltin the_PassConv) [varCT a]
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
        

streamReturnType = mkConType $ do
  e <- newAnonymousVariable TypeLevel
  a <- newAnonymousVariable TypeLevel
  addr_pc <- newAnonymousVariable ObjectLevel
  let pc_type = appCT (conCT $ pyonBuiltin the_PassConv) [varCT a]
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

passConvOwnedType = mkConType $ do
  a <- newAnonymousVariable TypeLevel
  let result_type =
        appCT (conCT $ pyonBuiltin the_PassConv) [varCT a]
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
      element_passconv_type =
        appCT (conCT $ pyonBuiltin the_PassConv) [varCT a]
      result_type =
        appCT (conCT $ pyonBuiltin the_PassConv) [stream_type]
      constructor_type =
        funCT $
        pureArrCT (ValPT (Just a) ::: expCT pureKindE) $
        pureArrCT (ReadPT addr1 ::: element_passconv_type) $
        retCT (WriteRT ::: result_type)
  return (OwnRT ::: constructor_type)

constructorTable =
  IntMap.fromList [(fromIdent $ conID c, ty) | (c, ty) <- table]
  where
    table = [ (pyonBuiltin the_passConv_int,
               ReadRT (mkInternalVarE $ pyonBuiltin the_passConv_int_addr) ::: appCT (conCT $ pyonBuiltin the_PassConv) [conCT $ pyonBuiltin the_int])
            , (pyonBuiltin the_passConv_owned,
               passConvOwnedType)
            , (pyonBuiltin the_passConv_iter,
               passConvIterType)
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
            , (pyonBuiltin (zeroMember . the_AdditiveDict_int),
               zeroIntOpType)
            , (pyonBuiltin (addMember . the_AdditiveDict_int),
               binaryIntOpType)
            , (pyonBuiltin (subMember . the_AdditiveDict_int),
               binaryIntOpType)
            , (pyonBuiltin (zeroMember . the_AdditiveDict_float),
               zeroFloatOpType)
            , (pyonBuiltin (addMember . the_AdditiveDict_float),
               binaryFloatOpType)
            , (pyonBuiltin (subMember . the_AdditiveDict_float),
               binaryFloatOpType)
            , (pyonBuiltin (traverseMember . the_TraversableDict_list),
               listTraverseType)
            , (pyonBuiltin (buildMember . the_TraversableDict_list),
               makelistType)
            , (pyonBuiltin (traverseMember . the_TraversableDict_Stream),
               streamIdType)
            , (pyonBuiltin (buildMember . the_TraversableDict_Stream),
               streamIdType)
            , (pyonBuiltin the_additiveDict,
               additiveDictType)
            , (getPyonTupleCon' 2,
               tuple2ConType)
            , (pyonBuiltin SystemF.Builtins.the_fun_copy,
               copyType)
            , (pyonBuiltin SystemF.Builtins.the_oper_CAT_MAP,
               streamBindType)
            , (pyonBuiltin SystemF.Builtins.the_fun_return,
               streamReturnType)
            ]
