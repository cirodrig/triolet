{-| Generate type info by calling compiler-generated functions
-}

module SystemF.Datatypes.InfoCall
       (constructSizeParameter,
        constructKnownSizeParameter,
        constructConstantSizeParameter,
        callUnboxedInfoFunction,
        callKnownUnboxedInfoFunction,
        callConstantUnboxedInfoFunction,
        callBoxedInfoFunction,
        callConstantBoxedInfoFunction)
where

import Prelude hiding(catch)

import Control.Exception
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import qualified Data.IntMap as IntMap
import Data.List
import Data.Maybe
import Data.Monoid
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.Supply
import qualified LowLevel.Types as LL
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.Datatypes.DynamicTypeInfo
import SystemF.Datatypes.Structure
import SystemF.Datatypes.Util(tagType)
import SystemF.Datatypes.Layout
import SystemF.Datatypes.Code
import Type.Type
import Type.Environment
import Type.Eval

constructKnownSizeParameter :: CoreDynTypeInfo -> KindedType -> Gen ExpM
constructKnownSizeParameter type_info kty = do
  m_e <- constructSizeParameter type_info kty
  case m_e of
    Nothing -> internalError "constructKnownSizeParameter"
    Just e  -> return e

constructConstantSizeParameter :: KindedType -> Gen (Maybe ExpM)
constructConstantSizeParameter kty =
  constructSizeParameter emptyTypeInfo kty

callKnownUnboxedInfoFunction :: CoreDynTypeInfo -> DataType -> [Type] -> Gen ExpM
callKnownUnboxedInfoFunction type_info data_type ty_args = do
  m_e <- callUnboxedInfoFunction type_info data_type ty_args
  case m_e of
    Nothing -> internalError "callKnownUnboxedInfoFunction"
    Just e  -> return e

callConstantUnboxedInfoFunction :: DataType -> [Type] -> Gen (Maybe ExpM)
callConstantUnboxedInfoFunction data_type ty_args =
  callUnboxedInfoFunction emptyTypeInfo data_type ty_args

callConstantBoxedInfoFunction :: DataConType -> [Type] -> [Type]
                              -> Gen (Maybe ExpM)
callConstantBoxedInfoFunction dcon_type ty_args ex_types =
  callBoxedInfoFunction emptyTypeInfo dcon_type ty_args ex_types

-------------------------------------------------------------------------------
-- Recursively constructing structures

-- | Call auto-generated global functions to construct info for a type.
--   Return 'Nothing' if there's not enough dynamic information to construct 
--   the info.
constructInfo :: CoreDynTypeInfo -> KindedType -> Gen (Maybe ExpM)
constructInfo type_info (KindedType k t) =
  case k
  of BareK   -> constructBareInfo type_info t
     ValK    -> constructValInfo type_info t

constructBareInfo type_info ty = constructBareInfo' build type_info ty
  where
    build :: Either BareInfo ExpM -> Gen ExpM
    build (Right e)  = return e
    build (Left rep) = return $ packRepr ty rep

constructValInfo type_info ty = constructValInfo' build type_info ty
  where
    build (Right e)  = return e
    build (Left rep) = return $ packReprVal ty rep

-- | Call auto-generated global functions to construct sizes for an unboxed
--   type.
--   Return 'Nothing' if there's not enough dynamic information to construct 
--   the info.
constructSizeParameter :: CoreDynTypeInfo -> KindedType -> Gen (Maybe ExpM)
constructSizeParameter type_info (KindedType k t) =
  case k
  of BareK     -> constructBareSizeParameter type_info t
     ValK      -> constructValSizeParameter type_info t
     IntIndexK -> internalError "constructSizeParameter: Not implemented"

constructBareSizeParameter type_info ty = constructBareInfo' build type_info ty
  where
    build (Right e)  = build . Left =<< unpackRepr ty e
    build (Left rep) = return $ packSizeAlign ty $ bare_info_size rep

constructValSizeParameter type_info ty = constructValInfo' build type_info ty
  where
    build (Right e)  = build . Left =<< unpackReprVal ty e
    build (Left rep) = return $ packSizeAlignVal ty $ val_info_size rep

-- | Invoke the constructor function to compute the dynamic type information
--   of a bare data structure.
--   Return 'Nothing' if there's not enough dynamic information to construct 
--   the info.
constructBareInfo' :: (Either BareInfo ExpM -> Gen a)
                   -> CoreDynTypeInfo -> Type -> Gen (Maybe a)
constructBareInfo' mk_result type_info ty =
  condM (lift $ reduceToWhnf ty)
  [ -- Type constructor: Call the generated function
    do Just (op, args) <- liftM fromVarApp it
       Just data_type <- lift $ lookupDataType op
       lift $ do
         m_info_exp <- callUnboxedInfoFunction type_info data_type args
         case m_info_exp of
           Nothing -> return Nothing
           Just e  -> fmap Just $ mk_result $ Right e

    -- Variable: look it up in the environment
  , do ty' <- it
       lift $ do
         m_info <- lift $ lookupBareTypeInfo type_info ty'
         case m_info of
           Nothing -> return Nothing
           Just i  -> fmap Just $ mk_result $ Left i
  ]

-- | Invoke the constructor function to compute the dynamic type information
--   of a value data structure
constructValInfo' :: (Either ValInfo ExpM -> Gen a)
                  -> CoreDynTypeInfo -> Type -> Gen (Maybe a)
constructValInfo' mk_result type_info ty =
  condM (lift $ reduceToWhnf ty)
  [ -- Type constructor: Call the generated function
    do Just (op, args) <- liftM fromVarApp it
       Just data_type <- lift $ lookupDataType op
       lift $ do
         m_info_exp <- callUnboxedInfoFunction type_info data_type args
         case m_info_exp of
           Nothing -> return Nothing
           Just e  -> fmap Just $ mk_result $ Right e

    -- Variable: look it up in the environment
  , do ty' <- it
       lift $ do
         m_info <- lift $ lookupValTypeInfo type_info ty'
         case m_info of
           Nothing -> return Nothing
           Just i -> fmap Just $ mk_result $ Left i
  ]

-- | Generate a call to an unboxed type constructor's info function
callUnboxedInfoFunction :: CoreDynTypeInfo -> DataType -> [Type]
                        -> Gen (Maybe ExpM)
callUnboxedInfoFunction type_info data_type ty_args = do
  -- Get size parameters and static types for this constructor
  size_param_types <- lift $ instantiateSizeParams data_type ty_args
  static_types <- lift $ instantiateStaticTypes data_type ty_args
  m_args <- mapM (constructInfo type_info) $ size_param_types ++ static_types

  -- Create a constructor call
  return $ do
    args <- sequence m_args
    return $ varAppE' (dataTypeUnboxedInfoVar data_type) ty_args args

-- | Generate a call to a boxed type constructor's info function
callBoxedInfoFunction :: CoreDynTypeInfo -> DataConType -> [Type] -> [Type]
                      -> Gen (Maybe ExpM)
callBoxedInfoFunction type_info dcon_type ty_args ex_types = do
  let data_type = dataConType dcon_type
      con = dataConCon dcon_type

  -- Get size parameters and static types for this constructor
  size_param_types <- lift $ instantiateSizeParams data_type ty_args
  static_types <- lift $ instantiateStaticTypes data_type ty_args
  m_args <- mapM (constructInfo type_info) $ size_param_types ++ static_types

  -- Create a constructor call
  return $ do
    args <- sequence m_args
    return $ varAppE' (dataTypeBoxedInfoVar data_type con) (ty_args ++ ex_types) args

