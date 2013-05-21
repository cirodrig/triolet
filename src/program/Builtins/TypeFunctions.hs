
{-# LANGUAGE Rank2Types, TemplateHaskell #-}
module Builtins.TypeFunctions(builtinTypeFunctions) where

import Control.Monad
import Data.Array
import qualified Data.Map as Map
import Language.Haskell.TH(mkName, dataD, cxt, Dec(DataD), Con(NormalC))
import Text.PrettyPrint.HughesPJ

import Builtins.BuiltinsTH
import Common.MonadLogic
import Common.Error
import Type.Type
import Type.Environment
import Type.Compare
import Type.Eval

-------------------------------------------------------------------------------
-- The builtin module may not be available while evaluating type functions,
-- so any needed variables are looked up from the type environment.

$(do let cons = [mkName ("The_" ++ nm)
                | nm <- builtinTypeNamesForTypeFunctions]
         num_cons = length cons
         con_decls = [return $ NormalC c [] | c <- cons]

     -- Declare a data type
     data_decl <-
       dataD (cxt []) (mkName "BuiltinThing") [] con_decls [mkName "Enum"]

     return [data_decl])

-- | Look up builtin variable names and insert them into the array
createBuiltinsArray :: Map.Map String Var -> Array Int Var
createBuiltinsArray name_environment =
  -- Force evaluation of all array elements, then return the array
  foldr seq builtin_array $ elems builtin_array
  where
    -- Look up each builtin type and variable
    get_variable level name =
      case Map.lookup name name_environment
      of Just v
           | getLevel v == level -> v
           | otherwise -> internalError $
                          "Wrong level for builtin variable: " ++ name
         Nothing -> internalError $ "Missing builtin variable: " ++ name

    builtin_list =
      map (get_variable TypeLevel) builtinTypeNamesForTypeFunctions

    builtin_array = listArray (0, num_builtins-1) builtin_list

    num_builtins = length builtinTypeNamesForTypeFunctions

getBuiltin :: Array Int Var -> BuiltinThing -> Var
getBuiltin builtins thing = builtins ! fromEnum thing

isBuiltin :: Array Int Var -> BuiltinThing -> Var -> Bool
isBuiltin builtins thing v = v == getBuiltin builtins thing

-------------------------------------------------------------------------------

-- | A type function based on the shape of a container of type @(box -> box)@.
--   Attempt to compute a shape based on the deconstructed, fully applied
--   type.
shapeLike :: Array Int Var
          -> (forall m. EvalMonad m => Var -> [Type] -> m (Maybe Type))
          -> TypeFunction
shapeLike bi f = typeFunction 1 compute_shape
  where
    compute_shape :: forall m. EvalMonad m => [Type] -> m Type
    compute_shape (container_type : other_types) = do
      -- Apply to produce a type of kind box, which can be fully evaluated
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
          return $ varApp (getBuiltin bi The_shape) (container_type : other_types)

-- Create a 1D array shape expression
array_shape bi sh =
  varApp (getBuiltin bi The_arr_shape) [sh, VarT $ getBuiltin bi The_dim0]

-- | Construct the builtin type functions. 
--   The type variables referenced by builtin type functions are passed in
--   as parameters.
builtinTypeFunctions :: Map.Map String Var
                     -> Map.Map String BuiltinTypeFunction
builtinTypeFunctions name_environment =
  let bi = createBuiltinsArray name_environment
  in Map.fromList
     [ (name, BuiltinTypeFunction (pure_f bi) (spec_f bi) (mem_f bi))
     | (name, pure_f, spec_f, mem_f) <-
          [ ("minus_i", minusTF, minusTF, minusTF)
          , ("plus_i", plusTF, minusTF, plusTF)
          , ("min_i", minTF, minusTF, minTF)
          , ("max_i", maxTF, minusTF, maxTF)
          , ("shape", shapePureTF, idTF The_shape 1, shapeMemTF)
          , ("cartesianDomain", cartPureTF, idTF The_cartesianDomain 1, cartMemTF)
          , ("index", indexPureTF, idTF The_index 1, indexMemTF)
          , ("offset", offsetPureTF, idTF The_offset 1, offsetMemTF)
          , ("slice", slicePureTF, idTF The_slice 1, sliceMemTF)
          --, ("Stream", streamPureTF, idTF The_Stream 1, streamMemTF)

            -- Use the same function in mem and spec
          , ("AsBox", boxedPureTF, boxedMemTF, boxedMemTF)
          , ("AsBare", barePureTF, bareMemTF, bareMemTF)
          ]]

-- | A type function that doesn't get reduced at all
idTF :: BuiltinThing -> Int -> Array Int Var -> TypeFunction
idTF get_con arity bi =
  let con = getBuiltin bi get_con
  in con `seq` typeFunction arity $ \args -> return $ varApp con args

-- | The integers extended with @+infinity@ and @-infinity@
data ExtInt = Fin Integer | NegInf | PosInf deriving(Eq)

fin0 = Fin 0

toExtInt ty = do
  ty' <- reduceToWhnf ty
  return $! case ty'
            of IntT n                  -> Just (Fin n)
               VarT v | v == posInftyV -> Just PosInf
                      | v == negInftyV -> Just NegInf
               _                       -> Nothing

toExtInt' ty default_value k = do
  x <- toExtInt ty
  case x of
    Nothing -> return default_value
    Just y  -> k y

fromExtInt (Fin n) = IntT n
fromExtInt NegInf = VarT negInftyV
fromExtInt PosInf = VarT posInftyV

binaryIntTF :: Var
            -> Maybe ExtInt     -- ^ Left unit
            -> Maybe ExtInt     -- ^ Right unit
            -> (ExtInt -> ExtInt -> Maybe ExtInt)
            -> TypeFunction
{-# INLINE binaryIntTF #-}
binaryIntTF operator left_unit right_unit f = typeFunction 2 $ \args ->
  case args
  of [arg1, arg2] -> do
       -- Reduce arguments to WHNF first
       whnf_arg1 <- reduceToWhnf arg1
       whnf_arg2 <- reduceToWhnf arg2
       let can't_reduce = varApp operator [whnf_arg1, whnf_arg2]

       maff1 <- toExtInt whnf_arg1
       case maff1 of
         Nothing ->
           -- First argument is unknown.  Is the second argument a unit? 
           case right_unit
           of Nothing -> return can't_reduce
              Just u -> do
                -- Is the second argument a unit?
                maff2 <- toExtInt whnf_arg2
                case maff2 of
                  Just aff2 | aff2 == u ->
                    return whnf_arg1
                  _ ->
                    return can't_reduce

         Just aff1 ->
           -- Is the first argument a unit?
           case left_unit
           of Just u | u == aff1 ->
                return whnf_arg2
              _ ->
                -- Attempt to evaluate
                toExtInt' whnf_arg2 can't_reduce $ \aff2 ->
                return $! case f aff1 aff2
                          of Just aff -> fromExtInt aff
                             Nothing -> can't_reduce
     _ -> return $ varApp operator args

-- | Subtract type-level integers.
--   This function works the same in System F and Mem.
minusTF bi =
  binaryIntTF (getBuiltin bi The_minus_i) (Just fin0) (Just fin0) function
  where
    function (Fin x) (Fin y) = Just (Fin (x - y))
    function (Fin _) NegInf  = Just PosInf
    function (Fin _) PosInf  = Just NegInf
    function NegInf  NegInf  = Nothing
    function NegInf  _       = Just NegInf
    function PosInf  PosInf  = Nothing
    function PosInf  _       = Just PosInf

-- | Add type-level integers.
--   This function works the same in System F and Mem.
plusTF bi =
  binaryIntTF (getBuiltin bi The_plus_i) (Just fin0) (Just fin0) function
  where
    function (Fin x) (Fin y) = Just (Fin (x + y))
    function (Fin _) NegInf  = Just NegInf
    function (Fin _) PosInf  = Just PosInf
    function NegInf  PosInf  = Nothing
    function NegInf  _       = Just NegInf
    function PosInf  NegInf  = Nothing
    function PosInf  _       = Just PosInf

-- | Take the minimum of type-level integers.
--   This function works the same in System F and Mem.
minTF bi =
  binaryIntTF (getBuiltin bi The_min_i) (Just PosInf) (Just PosInf) function
  where
    function (Fin x) (Fin y) = Just (Fin (min x y))
    function _       NegInf  = Just NegInf
    function x       PosInf  = Just x
    function NegInf  _       = Just NegInf
    function PosInf  x       = Just x

-- | Take the maximum of type-level integers.
--   This function works the same in System F and Mem.
maxTF bi =
  binaryIntTF (getBuiltin bi The_max_i) (Just NegInf) (Just NegInf) function
  where
    function (Fin x) (Fin y) = Just (Fin (max x y))
    function _       PosInf  = Just PosInf
    function x       NegInf  = Just x
    function PosInf  _       = Just PosInf
    function NegInf  x       = Just x

-- | Compute the shape of a data type in the pure type system
shapePureTF bi = shapeLike bi $ \op args ->
  case () of
    () | isBuiltin bi The_Stream op ->
           case args of [arg, _] -> liftM Just $ reduceToWhnf arg
       | isBuiltin bi The_view op ->
           case args of [arg, _] -> liftM Just $ reduceToWhnf arg
       | isBuiltin bi The_list op -> return_list_dim
       | isBuiltin bi The_array0 op -> return_dim0
       | isBuiltin bi The_array1 op -> return_dim1
       | isBuiltin bi The_array2 op -> return_dim2
       | isBuiltin bi The_array3 op -> return_dim3
       | isBuiltin bi The_blist op -> return_list_dim
       | isBuiltin bi The_barray1 op -> return_dim1
       | isBuiltin bi The_barray2 op -> return_dim2
       | isBuiltin bi The_barray3 op -> return_dim3
       | isBuiltin bi The_llist op -> return_list_dim
    _ -> return Nothing
  where
    return_list_dim, return_dim0, return_dim1, return_dim2, return_dim3 :: EvalMonad m => m (Maybe Type)
    return_list_dim = return $ Just $ VarT (getBuiltin bi The_list_dim)
    return_dim0 = return $ Just $ VarT (getBuiltin bi The_dim0)
    return_dim1 = return $ Just $ VarT (getBuiltin bi The_dim1)
    return_dim2 = return $ Just $ VarT (getBuiltin bi The_dim2)
    return_dim3 = return $ Just $ VarT (getBuiltin bi The_dim3)

cartPureTF bi = typeFunction 1 $ \[index_type] -> do
  index_type' <- reduceToWhnf index_type
  let can't_reduce =
        return $ varApp (getBuiltin bi The_cartesianDomain) [index_type]
  case fromVarApp index_type' of
    Just (op, [])
      | isBuiltin bi The_NoneType op -> return_dim0
      | op == intV -> return_dim1
    Just (op, [t1, t2])
      | isBuiltin bi The_Tuple2 op ->
          ifM (is_int t1 >&&> is_int t2) return_dim2 can't_reduce
    Just (op, [t1, t2, t3])
      | isBuiltin bi The_Tuple3 op ->
          ifM (is_int t1 >&&> is_int t2 >&&> is_int t3) return_dim3 can't_reduce
    _ -> can't_reduce
  where
    is_int :: EvalMonad m => Type -> m Bool
    is_int ty = do
      ty' <- reduceToWhnf ty
      return $! case ty'
                of VarT v -> v == intV
                   _      -> False
    return_dim0, return_dim1, return_dim2, return_dim3 :: EvalMonad m => m Type
    return_dim0 = return $ VarT (getBuiltin bi The_dim0)
    return_dim1 = return $ VarT (getBuiltin bi The_dim1)
    return_dim2 = return $ VarT (getBuiltin bi The_dim2)
    return_dim3 = return $ VarT (getBuiltin bi The_dim3)

cartMemTF bi = typeFunction 1 $ \[index_type] -> do
  index_type' <- reduceToWhnf index_type
  let can't_reduce =
        return $ varApp (getBuiltin bi The_cartesianDomain) [index_type]
  case fromVarApp index_type' of
    Just (op, [arg_ty])
      | op == storedV -> do
           arg_ty' <- reduceToWhnf arg_ty
           case fromVarApp arg_ty' of
             Just (op, [])
               | isBuiltin bi The_NoneType op -> return_dim0
               | op == intV -> return_dim1
             _ -> can't_reduce
    Just (op, [t1, t2])
      | isBuiltin bi The_Tuple2 op ->
          ifM (is_int t1 >&&> is_int t2) return_dim2 can't_reduce
    Just (op, [t1, t2, t3])
      | isBuiltin bi The_Tuple3 op ->
          ifM (is_int t1 >&&> is_int t2 >&&> is_int t3) return_dim3 can't_reduce
    _ -> can't_reduce
  where
    is_int :: EvalMonad m => Type -> m Bool
    is_int ty = do
      ty' <- reduceToWhnf ty
      case fromVarApp ty' of
        Just (op, [arg_ty]) 
          | op == storedV -> do
              arg_ty' <- reduceToWhnf arg_ty
              return $! case arg_ty'
                        of VarT v -> v == intV
                           _      -> False
        _ -> return False

    return_dim0, return_dim1, return_dim2, return_dim3 :: EvalMonad m => m Type
    return_dim0 = return $ VarT (getBuiltin bi The_dim0)
    return_dim1 = return $ VarT (getBuiltin bi The_dim1)
    return_dim2 = return $ VarT (getBuiltin bi The_dim2)
    return_dim3 = return $ VarT (getBuiltin bi The_dim3)

-- | Compute the shape of a data type in the memory type system
shapeMemTF bi = shapeLike bi $ \op args ->
  case () of
    () | isBuiltin bi The_Boxed op ->
           case args
           of [arg] -> examine_bare_type =<< reduceToWhnf arg
       | isBuiltin bi The_Stream op ->
           case args of [shape, _] -> return_shape shape
       | isBuiltin bi The_view op ->
           case args of [shape, _] -> return_shape shape
       | isBuiltin bi The_llist op -> return_list_dim
    _ -> return Nothing
  where
    return_shape :: EvalMonad m => Type -> m (Maybe Type)
    return_shape sh = liftM Just (reduceToWhnf sh)

    -- Type was of the form @Boxed (t a)@
    -- Examine the argument type, 't'
    examine_bare_type :: EvalMonad m => Type -> m (Maybe Type)
    examine_bare_type ty = 
      case fromVarApp ty
      of Just (op, [_])
           | isBuiltin bi The_list op -> return_list_dim
           | isBuiltin bi The_array0 op -> return_dim0
           | isBuiltin bi The_array1 op -> return_dim1
           | isBuiltin bi The_array2 op -> return_dim2
           | isBuiltin bi The_array3 op -> return_dim3
           | isBuiltin bi The_blist op -> return_list_dim
           | isBuiltin bi The_barray1 op -> return_dim1
           | isBuiltin bi The_barray2 op -> return_dim2
           | isBuiltin bi The_barray3 op -> return_dim3
         _ -> return Nothing

    return_list_dim, return_dim0, return_dim1, return_dim2, return_dim3 :: EvalMonad m => m (Maybe Type)
    return_list_dim = return $ Just $ VarT (getBuiltin bi The_list_dim)
    return_dim0 = return $ Just $ VarT (getBuiltin bi The_dim0)
    return_dim1 = return $ Just $ VarT (getBuiltin bi The_dim1)
    return_dim2 = return $ Just $ VarT (getBuiltin bi The_dim2)
    return_dim3 = return $ Just $ VarT (getBuiltin bi The_dim3)

indexPureTF bi = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator [shape_arg] = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | isBuiltin bi The_list_dim op -> return int_type
           | isBuiltin bi The_dim0 op -> return none_type
           | isBuiltin bi The_dim1 op -> return int_type
           | isBuiltin bi The_dim2 op -> return int2_type
           | isBuiltin bi The_dim3 op -> return int3_type
        _ -> return $ varApp (getBuiltin bi The_index) [shape_arg']

    none_type = VarT (getBuiltin bi The_NoneType)
    int_type = intT
    int2_type = varApp (getBuiltin bi The_Tuple2) [int_type, int_type]
    int3_type = varApp (getBuiltin bi The_Tuple3) [int_type, int_type, int_type]

indexMemTF bi = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator [shape_arg] = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | isBuiltin bi The_list_dim op -> return int_type
           | isBuiltin bi The_dim0 op -> return none_type
           | isBuiltin bi The_dim1 op -> return int_type
           | isBuiltin bi The_dim2 op -> return int2_type
           | isBuiltin bi The_dim3 op -> return int3_type
        _ -> return $ varApp (getBuiltin bi The_index) [shape_arg']

    compute_eliminator ts =
      internalError "Error in type application when reducing a type function"

    none_type = varApp storedV [VarT (getBuiltin bi The_NoneType)]
    int_type = varApp storedV [intT]
    int2_type = varApp (getBuiltin bi The_Tuple2)
                [int_type, int_type]
    int3_type = varApp (getBuiltin bi The_Tuple3)
                [int_type, int_type, int_type]

offsetPureTF bi = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator [shape_arg] = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | isBuiltin bi The_list_dim op -> return int_type
           | isBuiltin bi The_dim0 op -> return none_type
           | isBuiltin bi The_dim1 op -> return none_type
           | isBuiltin bi The_dim2 op -> return none_type
           | isBuiltin bi The_dim3 op -> return none_type
        _ -> return $ varApp (getBuiltin bi The_index) [shape_arg']

    none_type = VarT (getBuiltin bi The_NoneType)
    int_type = intT

offsetMemTF bi = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator [shape_arg] = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | isBuiltin bi The_list_dim op -> return int_type
           | isBuiltin bi The_dim0 op -> return none_type
           | isBuiltin bi The_dim1 op -> return none_type
           | isBuiltin bi The_dim2 op -> return none_type
           | isBuiltin bi The_dim3 op -> return none_type
        _ -> return $ varApp (getBuiltin bi The_index) [shape_arg']

    compute_eliminator ts =
      internalError "Error in type application when reducing a type function"

    none_type = varApp storedV [VarT (getBuiltin bi The_NoneType)]
    int_type = varApp storedV [intT]

slicePureTF bi = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator [shape_arg] = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | isBuiltin bi The_list_dim op -> return slice_type
           | isBuiltin bi The_dim0 op -> return none_type
           | isBuiltin bi The_dim1 op -> return slice_type
           | isBuiltin bi The_dim2 op -> return slice2_type
           | isBuiltin bi The_dim3 op -> return slice3_type
        _ -> return $ varApp (getBuiltin bi The_slice) [shape_arg']

    none_type = VarT (getBuiltin bi The_NoneType)
    slice_type = VarT (getBuiltin bi The_SliceObject)
    slice2_type = varApp (getBuiltin bi The_Tuple2)
                  [slice_type, slice_type]
    slice3_type = varApp (getBuiltin bi The_Tuple3)
                  [slice_type, slice_type, slice_type]

sliceMemTF bi = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator [shape_arg] = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | isBuiltin bi The_list_dim op -> return slice_type
           | isBuiltin bi The_dim0 op -> return none_type
           | isBuiltin bi The_dim1 op -> return slice_type
           | isBuiltin bi The_dim2 op -> return slice2_type
           | isBuiltin bi The_dim3 op -> return slice3_type
        _ -> return $ varApp (getBuiltin bi The_slice) [shape_arg']

    none_type = varApp storedV [VarT (getBuiltin bi The_NoneType)]
    slice_type = VarT (getBuiltin bi The_SliceObject)
    slice2_type = varApp (getBuiltin bi The_Tuple2)
                  [slice_type, slice_type]
    slice3_type = varApp (getBuiltin bi The_Tuple3)
                  [slice_type, slice_type, slice_type]

-- | The 'AsBox' data type should never appear in the pure type system
boxedPureTF bi =
  typeFunction 1 (\_ -> internalError "Unexpected occurrence of 'AsBox'")

-- | Compute the boxed representation corresponding to a bare type
--   This is used for both spec and mem types.
boxedMemTF bi = typeFunction 1 compute_boxed
  where
    compute_boxed :: forall m. EvalMonad m => [Type] -> m Type
    compute_boxed [arg_type] =
      -- Evaluate and inspect the argument
      eval =<< reduceToWhnf arg_type

    compute_boxed args =
      internalError $ "Kind error in application of 'AsBox' (" ++ show (sep (punctuate (text ",") $ map pprType args)) ++ ")"


    eval :: forall m. EvalMonad m => Type -> m Type
    eval arg =
      case fromVarApp arg
      of Just (op, args')
           | isBuiltin bi The_AsBare op ||
             op == refV ->
               -- AsBox (AsBare t)   =  t
               -- AsBox (StoredBox t)  =  t
               case args'
               of [arg'] -> reduceToWhnf arg'

           | otherwise -> do
               -- If the argument is a data constructor application, then
               -- use 'Boxed' as the adapter type
               m_dtype <- lookupDataType op
               case m_dtype of
                 Just _ -> return $ varApp (getBuiltin bi The_Boxed) [arg]
                 _ -> cannot_reduce
         _ -> cannot_reduce
      where
        cannot_reduce =
          return $ varApp (getBuiltin bi The_AsBox) [arg]
          
-- | The 'BareType' data type should never appear in the pure type system
barePureTF bi =
  typeFunction 1 (\_ -> internalError "Unexpected occurrence of 'BareType'")

-- | Compute the bare representation corresponding to a boxed type.
--   This is used for both spec and mem types.
bareMemTF bi = typeFunction 1 compute_bare
  where
    compute_bare :: forall m. EvalMonad m => [Type] -> m Type
    compute_bare [arg_type] =
      -- Evaluate and inspect the argument
      eval =<< reduceToWhnf arg_type

    compute_bare args =
      internalError $ "Kind error in application of 'BareType' (" ++ show (sep (punctuate (text ",") $ map pprType args)) ++ ")"

    eval :: forall m. EvalMonad m => Type -> m Type
    eval arg =
      case arg
      of FunT {} -> stored_type -- Functions are naturally boxed
         AllT {} -> stored_type -- Forall'd types are naturally boxed
         _ -> case fromVarApp arg
              of Just (op, args')
                   | isBuiltin bi The_AsBox op ||
                     isBuiltin bi The_Boxed op ->
                       -- AsBare (AsBox t)  =  t
                       -- AsBare (Boxed t)      =  t
                       case args'
                       of [arg'] -> reduceToWhnf arg'

                   | isBuiltin bi The_Stream op ->
                       -- All fully applied 'Stream' types are naturally
                       -- boxed
                       stored_type
                          
                   | otherwise -> do
                       -- If the argument is a data constructor
                       -- application, then use 'StoredBox' as the
                       -- adapter type
                       m_dtype <- lookupDataType op
                       case m_dtype of
                         Just _ -> stored_type
                         _ -> cannot_reduce
                 _ -> cannot_reduce
      where
        stored_type =
          return $ varApp refV [arg]
        cannot_reduce =
          return $ varApp (getBuiltin bi The_AsBare) [arg]
