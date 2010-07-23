{-| Definitions of Core types of builtin constructors.
-}
module Pyon.Core.BuiltinTypes(conCoreType, conCoreReturnType)
where

import qualified Data.IntMap as IntMap
import System.IO.Unsafe

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Core
import Gluon.Eval.Environment
import Gluon.Eval.Eval
import Pyon.SystemF.Builtins
import Pyon.Core.Syntax
import Pyon.Core.Gluon
import Pyon.Core.Print

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

mkBinaryOpType :: RExp -> CBind CReturnT Rec
mkBinaryOpType ty =
  let constructor_type =
        funCT $
        pureArrCT (ValPT Nothing ::: expCT ty) $
        pureArrCT (ValPT Nothing ::: expCT ty) $
        retCT (ValRT ::: expCT ty)
  in OwnRT ::: constructor_type

binaryIntOpType = mkBinaryOpType $ mkInternalConE $ pyonBuiltin the_int
binaryFloatOpType = mkBinaryOpType $ mkInternalConE $ pyonBuiltin the_int

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
loadNoneTypeType = loadType $ expCT (mkInternalConE $ pyonBuiltin the_NoneType)
storeNoneTypeType = storeType $ expCT (mkInternalConE $ pyonBuiltin the_NoneType)
      
constructorTable =
  IntMap.fromList [(fromIdent $ conID c, ty) | (c, ty) <- table]
  where
    table = [ (pyonBuiltin the_passConv_int,
               ValRT ::: conCT (pyonBuiltin the_PassConv))
            , (pyonBuiltin Pyon.SystemF.Builtins.the_fun_store_int,
               storeIntType)
            , (pyonBuiltin Pyon.SystemF.Builtins.the_fun_load_int,
               loadIntType)
            , (pyonBuiltin Pyon.SystemF.Builtins.the_fun_store_float,
               storeFloatType)
            , (pyonBuiltin Pyon.SystemF.Builtins.the_fun_load_float,
               loadFloatType)
            , (pyonBuiltin Pyon.SystemF.Builtins.the_fun_store_NoneType,
               storeNoneTypeType)
            , (pyonBuiltin Pyon.SystemF.Builtins.the_fun_load_NoneType,
               loadNoneTypeType)
            , (pyonBuiltin (addMember . the_AdditiveDict_int),
               binaryIntOpType)
            , (pyonBuiltin (subMember . the_AdditiveDict_int),
               binaryIntOpType)
            , (pyonBuiltin (addMember . the_AdditiveDict_float),
               binaryFloatOpType)
            , (pyonBuiltin (subMember . the_AdditiveDict_float),
               binaryFloatOpType)
            , (getPyonTupleCon' 2,
               tuple2ConType)
            ]
