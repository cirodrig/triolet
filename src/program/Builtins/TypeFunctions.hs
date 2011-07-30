
module Builtins.TypeFunctions(builtinTypeFunctions) where

import qualified Data.Map as Map

import Builtins.Builtins
import Common.Error
import Type.Type
import Type.Environment
import Type.Compare
import Type.Eval

-- Create a 1D array shape expression
array_shape sh =
  varApp (pyonBuiltin the_array_shape) [sh, VarT $ pyonBuiltin the_unit_shape]

builtinTypeFunctions :: Map.Map Var BuiltinTypeFunction
builtinTypeFunctions =
  Map.fromList
  [ (pyonBuiltin the_shape, BuiltinTypeFunction shapePureTF shapeMemTF)
  , (pyonBuiltin the_Stream, BuiltinTypeFunction streamPureTF streamMemTF)
  , (pyonBuiltin the_BoxedType, BuiltinTypeFunction boxedPureTF boxedMemTF)
  , (pyonBuiltin the_BareType, BuiltinTypeFunction barePureTF bareMemTF)
  ]

-- | Compute the shape of a data type in the pure type system
shapePureTF = typeFunction 1 compute_shape
  where
    compute_shape :: forall m. EvalMonad m => [Type] -> m Type
    compute_shape [container_type] = do
      -- Apply to produce a type of kind *, which can be fully evaluated
      arg_type <- newAnonymousVar TypeLevel
      app_container_type <- reduceToWhnf (AppT container_type (VarT arg_type)) 
      simplify app_container_type container_type

    -- Pattern match against 'app_container_type'.  If nothing matches, then
    -- rebuild the original expression using 'container_type'.
    simplify :: forall m. EvalMonad m => Type -> Type -> m Type
    simplify app_container_type container_type = do
      case fromVarApp app_container_type of
        Just (op, args)
          | op `isPyonBuiltin` the_Stream || 
            op `isPyonBuiltin` the_LinStream ->
              case args of [arg, _] -> reduceToWhnf arg
          | op `isPyonBuiltin` the_MatrixStream ->
              case args of [_] -> return $ VarT (pyonBuiltin the_matrix_shape)
          | op `isPyonBuiltin` the_list ->
              return $ VarT (pyonBuiltin the_list_shape)
          | op `isPyonBuiltin` the_matrix ->
              return $ VarT (pyonBuiltin the_matrix_shape)
          | op `isPyonBuiltin` the_ListView ->
              return $ VarT (pyonBuiltin the_list_shape)
          | op `isPyonBuiltin` the_MatrixView ->
              return $ VarT (pyonBuiltin the_matrix_shape)
          | op `isPyonBuiltin` the_array ->
              case args
              of [arg, _] -> return $ array_shape arg
        _ -> cannot_reduce
      where
        cannot_reduce =
          return $ varApp (pyonBuiltin the_shape) [container_type]

-- | Compute the shape of a data type in the memory type system
shapeMemTF = typeFunction 1 compute_shape
  where
    compute_shape :: forall m. EvalMonad m => [Type] -> m Type
    compute_shape [container_type] = do
      -- Apply to produce a type of kind *, which can be fully evaluated
      arg_type <- newAnonymousVar TypeLevel
      app_container_type <- reduceToWhnf (AppT container_type (VarT arg_type)) 
      simplify app_container_type container_type

    -- Pattern match against 'app_container_type'.  If nothing matches, then
    -- rebuild the original expression using 'container_type'.
    simplify :: forall m. EvalMonad m => Type -> Type -> m Type
    simplify app_container_type container_type = do
      case fromVarApp app_container_type of
        Just (op, args)
          | op `isPyonBuiltin` the_StoredBox ->
              case args
              of [arg] ->
                   case fromVarApp arg 
                   of Just (op, [arg2, _]) 
                        | op `isPyonBuiltin` the_Stream ||
                          op `isPyonBuiltin` the_LinStream ->
                            reduceToWhnf arg2
                      Just (op, [_])
                        | op `isPyonBuiltin` the_MatrixStream ->
                            return $ VarT (pyonBuiltin the_matrix_shape)
                      _ -> cannot_reduce
          | op `isPyonBuiltin` the_list ->
              return $ VarT (pyonBuiltin the_list_shape)
          | op `isPyonBuiltin` the_matrix ->
              return $ VarT (pyonBuiltin the_matrix_shape)
          | op `isPyonBuiltin` the_ListView ->
              return $ VarT (pyonBuiltin the_list_shape)
          | op `isPyonBuiltin` the_MatrixView ->
              return $ VarT (pyonBuiltin the_matrix_shape)
          | op `isPyonBuiltin` the_array ->
              case args
              of [arg, _] -> return $ array_shape arg
        _ -> cannot_reduce
      where
        cannot_reduce =
          return $ varApp (pyonBuiltin the_shape) [container_type]

streamPureTF = typeFunction 1 compute_stream
  where
    compute_stream :: forall m. EvalMonad m => [Type] -> m Type
    compute_stream (shape_arg : other_args) = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | op `isPyonBuiltin` the_list_shape ||
             op `isPyonBuiltin` the_array_shape ||
             op `isPyonBuiltin` the_unit_shape ->
               return $ varApp (pyonBuiltin the_LinStream) (shape_arg' : other_args)
           | op `isPyonBuiltin` the_matrix_shape ->
               return $ varApp (pyonBuiltin the_MatrixStream) other_args
        _ -> return $ varApp (pyonBuiltin the_Stream) (shape_arg' : other_args)

streamMemTF = typeFunction 1 compute_stream
  where
    compute_stream :: forall m. EvalMonad m => [Type] -> m Type
    compute_stream (shape_arg : other_args) = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | op `isPyonBuiltin` the_list_shape ||
             op `isPyonBuiltin` the_array_shape ||
             op `isPyonBuiltin` the_unit_shape ->
               return $ varApp (pyonBuiltin the_LinStream) (shape_arg' : other_args)
           | op `isPyonBuiltin` the_matrix_shape ->
               return $ varApp (pyonBuiltin the_MatrixStream) other_args
        _ -> return $ varApp (pyonBuiltin the_Stream) (shape_arg' : other_args)

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
           | op `isPyonBuiltin` the_BareType ||
             op `isPyonBuiltin` the_StoredBox ->
               -- BoxedType (BareType t)   =  t
               -- BoxedType (StoredBox t)  =  t
               case args'
               of [arg'] -> reduceToWhnf arg'

           | otherwise -> do
               -- If the argument is a data constructor application, then
               -- use 'Boxed' as the adapter type
               tenv <- getTypeEnv
               case lookupDataType op tenv of
                 Just _ -> return $ varApp (pyonBuiltin the_Boxed) [arg]
                 _ -> cannot_reduce
         _ -> cannot_reduce
      where
        cannot_reduce =
          return $ varApp (pyonBuiltin the_BoxedType) [arg]
          
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
                   | op `isPyonBuiltin` the_BoxedType ||
                     op `isPyonBuiltin` the_Boxed ->
                       -- BareType (BoxedType t)  =  t
                       -- BareType (Boxed t)      =  t
                       case args'
                       of [arg'] -> reduceToWhnf arg'

                   | op `isPyonBuiltin` the_Stream ->
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
          return $ varApp (pyonBuiltin the_StoredBox) [arg]
        cannot_reduce =
          return $ varApp (pyonBuiltin the_BareType) [arg]
