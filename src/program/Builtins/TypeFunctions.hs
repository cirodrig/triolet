
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
    compute_shape [container_type] = reduceToWhnf container_type >>= simplify
    
    simplify container_type =
      case fromVarApp container_type of
        Just (op, args)
          | op `isPyonBuiltin` the_Stream ->
              case args of [arg] -> reduceToWhnf arg
          | op `isPyonBuiltin` the_list ->
              return $ VarT (pyonBuiltin the_list_shape)
          | op `isPyonBuiltin` the_array ->
              case args
              of [arg] -> return $ varApp (pyonBuiltin the_array_shape) [arg]
        _ ->
          -- Cannot reduce
          return $ varApp (pyonBuiltin the_shape) [container_type]
