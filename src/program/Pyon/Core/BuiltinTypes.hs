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
       internalError $ "lookupConstructorType: No information for constructor " ++ showLabel (conName c)

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

loadIntType = mkConType $ do
  a <- newAnonymousVariable ObjectLevel
  let int_type = expCT (mkInternalConE $ pyonBuiltin the_int)
      constructor_type =
        funCT $
        pureArrCT (ReadPT a ::: int_type) $
        retCT (ValRT ::: int_type)
  return (OwnRT ::: constructor_type)

storeIntType = mkConType $ do
  let int_type = expCT (mkInternalConE $ pyonBuiltin the_int)
      constructor_type =
        funCT $
        pureArrCT (ValPT Nothing ::: int_type) $
        retCT (WriteRT ::: int_type)
  return (OwnRT ::: constructor_type)

constructorTable =
  IntMap.fromList [(fromIdent $ conID c, ty) | (c, ty) <- table]
  where
    table = [ (pyonBuiltin the_passConv_int,
               ValRT ::: conCT (pyonBuiltin the_PassConv))
            , (pyonBuiltin (addMember . the_AdditiveDict_int),
               binaryIntOpType)
            , (getPyonTupleCon' 2,
               tuple2ConType)
            , (pyonBuiltin Pyon.SystemF.Builtins.the_fun_store_int,
               storeIntType)
            , (pyonBuiltin Pyon.SystemF.Builtins.the_fun_load_int,
               loadIntType)
            ]
