
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
  ]

-- | Compute the shape of a data type
shapeTF = typeFunction 1 compute_shape
  where
    compute_shape [container_type] = do
      -- Apply to produce a type of kind *, which can be fully evaluated
      arg_type <- newAnonymousVar TypeLevel
      app_container_type <- reduceToWhnf (AppT container_type (VarT arg_type)) 
      simplify app_container_type container_type

    -- Pattern match against 'app_container_type'.  If nothing matches, then
    -- rebuild the original expression using 'container_type'.
    simplify app_container_type container_type = do
      case fromVarApp app_container_type of
        Just (op, args)
          | op `isPyonBuiltin` the_BareType ->
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
