
module Builtins.TypeFunctions(builtinTypeFunctions) where

import qualified Data.Map as Map

import Builtins.Builtins
import Type.Type
import Type.Environment
import Type.Compare
import Type.Eval

builtinTypeFunctions :: Map.Map Var TypeFunction
builtinTypeFunctions =
  Map.fromList
  [ (pyonBuiltin the_shape, shapeTF)
  , (pyonBuiltin the_BoxedType, boxedTF)
  , (pyonBuiltin the_BareType, bareTF)
  ]

-- | Compute the shape of a data type
shapeTF = typeFunction 1 compute_shape
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
                        | op `isPyonBuiltin` the_Stream ->
                            reduceToWhnf arg2
                      _ -> cannot_reduce
          | op `isPyonBuiltin` the_list ->
              return $ VarT (pyonBuiltin the_list_shape)
          | op `isPyonBuiltin` the_array ->
              case args
              of [arg, _] ->
                   return $ varApp (pyonBuiltin the_array_shape) [arg]
        _ -> cannot_reduce
      where
        cannot_reduce =
          return $ varApp (pyonBuiltin the_shape) [container_type]

-- | Compute the boxed representation of a data type
boxedTF = typeFunction 1 compute_boxed
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
          
-- | Compute the bare representation of a type
bareTF = typeFunction 1 compute_bare
  where
    compute_bare :: forall m. EvalMonad m => [Type] -> m Type
    compute_bare [arg_type] =
      -- Evaluate and inspect the argument
      eval =<< reduceToWhnf arg_type

    eval :: forall m. EvalMonad m => Type -> m Type
    eval arg =
      case fromVarApp arg
      of Just (op, args')
           | op `isPyonBuiltin` the_BoxedType ||
             op `isPyonBuiltin` the_Boxed ->
               -- BareType (BoxedType t)  =  t
               -- BareType (Boxed t)      =  t
               case args'
               of [arg'] -> reduceToWhnf arg'

           | otherwise -> do
               -- If the argument is a data constructor application, then
               -- use 'StoredBox' as the adapter type
               tenv <- getTypeEnv
               case lookupDataType op tenv of
                 Just _ -> return $ varApp (pyonBuiltin the_StoredBox) [arg]
                 _ -> cannot_reduce
         _ -> cannot_reduce
      where
        cannot_reduce =
          return $ varApp (pyonBuiltin the_BareType) [arg]
