
{-# LANGUAGE Rank2Types #-}
module Builtins.TypeFunctions(builtinTypeFunctions) where

import Control.Monad
import qualified Data.Map as Map

import Builtins.Builtins
import Common.Error
import Type.Type
import Type.Environment
import Type.Compare
import Type.Eval

-- | A type function based on the shape of a container of type @(* -> *)@.
--   Attempt to compute a shape based on the deconstructed, fully applied
--   type.
shapeLike :: (forall m. EvalMonad m => Var -> [Type] -> m (Maybe Type))
          -> TypeFunction
shapeLike f = typeFunction 1 compute_shape
  where
    compute_shape :: forall m. EvalMonad m => [Type] -> m Type
    compute_shape (container_type : other_types) = do
      -- Apply to produce a type of kind *, which can be fully evaluated
      arg_type <- newAnonymousVar TypeLevel
      app_container_type <- reduceToWhnf (AppT container_type (VarT arg_type)) 
      case fromVarApp app_container_type of
        Just (op, args) -> do
          -- Try to evaluate by calling 'f'
          m_type <- f op args
          case m_type of
            Nothing -> cannot_reduce container_type
            Just t  -> return $ typeApp t other_types
        Nothing -> cannot_reduce container_type
      where
        cannot_reduce container_type =
          return $ varApp (pyonBuiltin The_shape) (container_type : other_types)

unpackArrayShapeArgs :: EvalMonad m => [Type] -> m [Type]
unpackArrayShapeArgs [size, next] = liftM (size :) $ unpackArrayShape next

unpackArrayShape :: EvalMonad m => Type -> m [Type]
unpackArrayShape ty = do
  ty' <- reduceToWhnf ty
  case fromVarApp ty' of
    Just (op, args)
      | op `isPyonBuiltin` The_arr_shape -> unpackArrayShapeArgs args
      | op `isPyonBuiltin` The_dim0 -> return []
    _ -> internalError "unpackArrayShape: Argument is not an array shape"

-- Create a 1D array shape expression
array_shape sh =
  varApp (pyonBuiltin The_arr_shape) [sh, VarT $ pyonBuiltin The_dim0]

builtinTypeFunctions :: Map.Map Var BuiltinTypeFunction
builtinTypeFunctions =
  Map.fromList
  [ (pyonBuiltin The_shape, BuiltinTypeFunction shapePureTF shapeMemTF)
  , (pyonBuiltin The_index, BuiltinTypeFunction indexPureTF indexMemTF)
  , (pyonBuiltin The_slice, BuiltinTypeFunction slicePureTF sliceMemTF)
  , (pyonBuiltin The_view, BuiltinTypeFunction viewPureTF viewMemTF)
  , (pyonBuiltin The_Stream, BuiltinTypeFunction streamPureTF streamMemTF)
  , (pyonBuiltin The_BoxedType, BuiltinTypeFunction boxedPureTF boxedMemTF)
  , (pyonBuiltin The_BareType, BuiltinTypeFunction barePureTF bareMemTF)
  ]

-- | Compute the shape of a data type in the pure type system
shapePureTF = shapeLike $ \op args ->
  case ()
  of () | op `isPyonBuiltin` The_Stream ->
            case args of [arg, _] -> liftM Just $ reduceToWhnf arg
        | op `isPyonBuiltin` The_Stream1 -> return_dim1
        | op `isPyonBuiltin` The_Sequence -> return_dim1
        | op `isPyonBuiltin` The_list -> return_dim1
        | op `isPyonBuiltin` The_array0 -> return_dim0
        | op `isPyonBuiltin` The_array1 -> return_dim1
        | op `isPyonBuiltin` The_array2 -> return_dim2
        | op `isPyonBuiltin` The_view0 -> return_dim0
        | op `isPyonBuiltin` The_view1 -> return_dim1
        | op `isPyonBuiltin` The_view2 -> return_dim2
        | op `isPyonBuiltin` The_array ->
            case args
            of [dim, _] -> do
                 dim' <- reduceToWhnf dim
                 case dim' of
                   VarT v | v `isPyonBuiltin` The_dim0 -> return_dim0
                          | v `isPyonBuiltin` The_dim1 -> return_dim1
                          | v `isPyonBuiltin` The_dim2 -> return_dim2
                   _ -> return Nothing
        | op `isPyonBuiltin` The_arr ->
            case args
            of [arg, _] -> return $ Just $ array_shape arg
     _ -> return Nothing
  where
    return_dim0, return_dim1, return_dim2 :: EvalMonad m => m (Maybe Type)
    return_dim0 = return $ Just $ VarT (pyonBuiltin The_dim0)
    return_dim1 = return $ Just $ VarT (pyonBuiltin The_dim1)
    return_dim2 = return $ Just $ VarT (pyonBuiltin The_dim2)

-- | Compute the shape of a data type in the memory type system
shapeMemTF = shapeLike $ \op args ->
  case ()
  of () | op `isPyonBuiltin` The_StoredBox ->
          case args
          of [arg] ->
               case fromVarApp arg 
               of Just (op, [arg2, _]) 
                    | op `isPyonBuiltin` The_Stream ->
                        liftM Just $ reduceToWhnf arg2
                  Just (op, [_])
                    | op `isPyonBuiltin` The_Stream1 -> return_dim1
                    | op `isPyonBuiltin` The_Sequence -> return_dim1
                    | op `isPyonBuiltin` The_view0 -> return_dim0
                    | op `isPyonBuiltin` The_view1 -> return_dim1
                    | op `isPyonBuiltin` The_view2 -> return_dim2
                  _ -> return Nothing
        | op `isPyonBuiltin` The_list -> return_dim1
        | op `isPyonBuiltin` The_array0 -> return_dim0
        | op `isPyonBuiltin` The_array1 -> return_dim1
        | op `isPyonBuiltin` The_array2 -> return_dim2
        | op `isPyonBuiltin` The_array ->
            case args
            of [arg, _] -> return $ Just $ array_shape arg
     _ -> return Nothing
  where
    return_dim0, return_dim1, return_dim2 :: EvalMonad m => m (Maybe Type)
    return_dim0 = return $ Just $ VarT (pyonBuiltin The_dim0)
    return_dim1 = return $ Just $ VarT (pyonBuiltin The_dim1)
    return_dim2 = return $ Just $ VarT (pyonBuiltin The_dim2)

indexPureTF = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator [shape_arg] = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | op `isPyonBuiltin` The_dim0 -> return none_type
           | op `isPyonBuiltin` The_dim1 -> return int_type
           | op `isPyonBuiltin` The_dim2 -> return int2_type
        _ -> return $ varApp (pyonBuiltin The_index) [shape_arg']

    none_type = VarT (pyonBuiltin The_NoneType)
    int_type = VarT (pyonBuiltin The_int)
    int2_type = varApp (pyonBuiltin The_PyonTuple2) [int_type, int_type]

indexMemTF = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator [shape_arg] = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | op `isPyonBuiltin` The_dim0 -> return none_type
           | op `isPyonBuiltin` The_dim1 -> return int_type
           | op `isPyonBuiltin` The_dim2 -> return int2_type
        _ -> return $ varApp (pyonBuiltin The_index) [shape_arg']

    none_type = varApp (pyonBuiltin The_Stored) [VarT (pyonBuiltin The_NoneType)]
    int_type = varApp (pyonBuiltin The_Stored) [VarT (pyonBuiltin The_int)]
    int2_type = varApp (pyonBuiltin The_PyonTuple2)
                [int_type, int_type]

slicePureTF = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator [shape_arg] = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | op `isPyonBuiltin` The_dim0 -> return none_type
           | op `isPyonBuiltin` The_dim1 -> return int3_type
           | op `isPyonBuiltin` The_dim2 -> return int6_type
        _ -> return $ varApp (pyonBuiltin The_slice) [shape_arg']

    none_type = VarT (pyonBuiltin The_NoneType)
    int_type = VarT (pyonBuiltin The_int)
    int3_type = varApp (pyonBuiltin The_PyonTuple3)
                [int_type, int_type, int_type]
    int6_type = varApp (pyonBuiltin The_PyonTuple2)
                [int3_type, int3_type]

sliceMemTF = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator [shape_arg] = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | op `isPyonBuiltin` The_dim0 -> return none_type
           | op `isPyonBuiltin` The_dim1 -> return slice_type
           | op `isPyonBuiltin` The_dim2 -> return slice2_type
        _ -> return $ varApp (pyonBuiltin The_slice) [shape_arg']

    none_type = VarT (pyonBuiltin The_NoneType)
    slice_type = VarT (pyonBuiltin The_SliceObject)
    slice2_type = varApp (pyonBuiltin The_PyonTuple2)
                  [slice_type, slice_type]

viewPureTF = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator (shape_arg : other_args) = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | op `isPyonBuiltin` The_dim0 ->
             return $ varApp (pyonBuiltin The_view0) other_args
           | op `isPyonBuiltin` The_dim1 ->
             return $ varApp (pyonBuiltin The_view1) other_args
           | op `isPyonBuiltin` The_dim2 ->
             return $ varApp (pyonBuiltin The_view2) other_args
        _ -> return $ varApp (pyonBuiltin The_view) (shape_arg' : other_args)

viewMemTF = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator (shape_arg : other_args) = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | op `isPyonBuiltin` The_dim0 ->
             return $ varApp (pyonBuiltin The_view0) other_args
           | op `isPyonBuiltin` The_dim1 ->
             return $ varApp (pyonBuiltin The_view1) other_args
           | op `isPyonBuiltin` The_dim2 ->
             return $ varApp (pyonBuiltin The_view2) other_args
        _ -> return $ varApp (pyonBuiltin The_view) (shape_arg' : other_args)

streamPureTF = typeFunction 1 compute_stream
  where
    compute_stream :: forall m. EvalMonad m => [Type] -> m Type
    compute_stream (shape_arg : other_args) = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
          | op `isPyonBuiltin` The_dim0 ->
              return_con The_view0 []
          | op `isPyonBuiltin` The_dim1 ->
              return_con The_Stream1 []
          | op `isPyonBuiltin` The_dim2 ->
              return_con The_view2 []
          | op `isPyonBuiltin` The_arr_shape -> do
              sizes <- unpackArrayShapeArgs args'
              case sizes of
                [size1] -> return_con The_darr1 [size1]
                [size1, size2] -> return_con The_darr2 [size1, size2]
        _ -> return_con The_Stream [shape_arg']
      where
        return_con :: forall m. EvalMonad m =>
                      BuiltinThing -> [Type] -> m Type
        return_con con args =
          return $ varApp (pyonBuiltin con) (args ++ other_args)

streamMemTF = typeFunction 1 compute_stream
  where
    compute_stream :: forall m. EvalMonad m => [Type] -> m Type
    compute_stream (shape_arg : other_args) = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
          | op `isPyonBuiltin` The_dim0 ->
              return_con The_view0 []
          | op `isPyonBuiltin` The_dim1 ->
              return_con The_Stream1 []
          | op `isPyonBuiltin` The_dim2 ->
              return_con The_view2 []
          | op `isPyonBuiltin` The_arr_shape -> do
              sizes <- unpackArrayShapeArgs args'
              case sizes of
                [size1] -> return_con The_darr1 [size1]
                [size1, size2] -> return_con The_darr2 [size1, size2]
        _ -> return_con The_Stream [shape_arg']
      where
        return_con :: forall m. EvalMonad m =>
                      BuiltinThing -> [Type] -> m Type
        return_con con args =
          return $ varApp (pyonBuiltin con) (args ++ other_args)

-- | The 'BoxedType' data type should never appear in the pure type system
boxedPureTF =
  typeFunction 1 (\_ -> internalError "Unexpected occurrence of 'BoxedType'")

-- | Compute the boxed representation corresponding to a bare type
boxedMemTF = typeFunction 1 compute_boxed
  where
    compute_boxed :: forall m. EvalMonad m => [Type] -> m Type
    compute_boxed [arg_type] =
      -- Evaluate and inspect the argument
      eval =<< reduceToWhnf arg_type

    eval :: forall m. EvalMonad m => Type -> m Type
    eval arg =
      case fromVarApp arg
      of Just (op, args')
           | op `isPyonBuiltin` The_BareType ||
             op `isPyonBuiltin` The_StoredBox ->
               -- BoxedType (BareType t)   =  t
               -- BoxedType (StoredBox t)  =  t
               case args'
               of [arg'] -> reduceToWhnf arg'

           | otherwise -> do
               -- If the argument is a data constructor application, then
               -- use 'Boxed' as the adapter type
               tenv <- getTypeEnv
               case lookupDataType op tenv of
                 Just _ -> return $ varApp (pyonBuiltin The_Boxed) [arg]
                 _ -> cannot_reduce
         _ -> cannot_reduce
      where
        cannot_reduce =
          return $ varApp (pyonBuiltin The_BoxedType) [arg]
          
-- | The 'BareType' data type should never appear in the pure type system
barePureTF =
  typeFunction 1 (\_ -> internalError "Unexpected occurrence of 'BareType'")

-- | Compute the bare representation corresponding to a boxed type
bareMemTF = typeFunction 1 compute_bare
  where
    compute_bare :: forall m. EvalMonad m => [Type] -> m Type
    compute_bare [arg_type] =
      -- Evaluate and inspect the argument
      eval =<< reduceToWhnf arg_type

    eval :: forall m. EvalMonad m => Type -> m Type
    eval arg =
      case arg
      of FunT {} -> stored_type -- Functions are naturally boxed
         AllT {} -> stored_type -- Forall'd types are naturally boxed
         _ -> case fromVarApp arg
              of Just (op, args')
                   | op `isPyonBuiltin` The_BoxedType ||
                     op `isPyonBuiltin` The_Boxed ->
                       -- BareType (BoxedType t)  =  t
                       -- BareType (Boxed t)      =  t
                       case args'
                       of [arg'] -> reduceToWhnf arg'

                   | op `isPyonBuiltin` The_Stream ->
                       -- All fully applied 'Stream' types are naturally
                       -- boxed
                       stored_type
                          
                   | otherwise -> do
                       -- If the argument is a data constructor
                       -- application, then use 'StoredBox' as the
                       -- adapter type
                       tenv <- getTypeEnv
                       case lookupDataType op tenv of
                         Just _ -> stored_type
                         _ -> cannot_reduce
                 _ -> cannot_reduce
      where
        stored_type =
          return $ varApp (pyonBuiltin The_StoredBox) [arg]
        cannot_reduce =
          return $ varApp (pyonBuiltin The_BareType) [arg]
