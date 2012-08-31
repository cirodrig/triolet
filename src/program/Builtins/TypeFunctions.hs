
{-# LANGUAGE Rank2Types #-}
module Builtins.TypeFunctions(builtinTypeFunctions) where

import Control.Monad
import qualified Data.Map as Map
import Text.PrettyPrint.HughesPJ

import Builtins.Builtins
import Common.MonadLogic
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
          return $ varApp (coreBuiltin The_shape) (container_type : other_types)

unpackArrayShapeArgs :: EvalMonad m => [Type] -> m [Type]
unpackArrayShapeArgs [size, next] = liftM (size :) $ unpackArrayShape next

unpackArrayShape :: EvalMonad m => Type -> m [Type]
unpackArrayShape ty = do
  ty' <- reduceToWhnf ty
  case fromVarApp ty' of
    Just (op, args)
      | op `isCoreBuiltin` The_arr_shape -> unpackArrayShapeArgs args
      | op `isCoreBuiltin` The_dim0 -> return []
    _ -> internalError "unpackArrayShape: Argument is not an array shape"

-- Create a 1D array shape expression
array_shape sh =
  varApp (coreBuiltin The_arr_shape) [sh, VarT $ coreBuiltin The_dim0]

builtinTypeFunctions :: Map.Map String BuiltinTypeFunction
builtinTypeFunctions =
  Map.fromList
  [ ("minus_i", BuiltinTypeFunction minusTF minusTF)
  , ("plus_i", BuiltinTypeFunction plusTF plusTF)
  , ("min_i", BuiltinTypeFunction minTF minTF)
  , ("max_i", BuiltinTypeFunction maxTF maxTF)
  , ("shape", BuiltinTypeFunction shapePureTF shapeMemTF)
  , ("cartesianDomain", BuiltinTypeFunction cartPureTF cartMemTF)
  , ("index", BuiltinTypeFunction indexPureTF indexMemTF)
  , ("slice", BuiltinTypeFunction slicePureTF sliceMemTF)
  , ("Stream", BuiltinTypeFunction streamPureTF streamMemTF)
  , ("BoxedType", BuiltinTypeFunction boxedPureTF boxedMemTF)
  , ("BareType", BuiltinTypeFunction barePureTF bareMemTF)
  ]

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
minusTF = binaryIntTF (coreBuiltin The_minus_i) (Just fin0) (Just fin0) function
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
plusTF = binaryIntTF (coreBuiltin The_plus_i) (Just fin0) (Just fin0) function
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
minTF = binaryIntTF (coreBuiltin The_min_i) (Just PosInf) (Just PosInf) function
  where
    function (Fin x) (Fin y) = Just (Fin (min x y))
    function _       NegInf  = Just NegInf
    function x       PosInf  = Just x
    function NegInf  _       = Just NegInf
    function PosInf  x       = Just x

-- | Take the maximum of type-level integers.
--   This function works the same in System F and Mem.
maxTF = binaryIntTF (coreBuiltin The_max_i) (Just NegInf) (Just NegInf) function
  where
    function (Fin x) (Fin y) = Just (Fin (max x y))
    function _       PosInf  = Just PosInf
    function x       NegInf  = Just x
    function PosInf  _       = Just PosInf
    function NegInf  x       = Just x

-- | Compute the shape of a data type in the pure type system
shapePureTF = shapeLike $ \op args ->
  case ()
  of () | op `isCoreBuiltin` The_Stream ->
            case args of [arg, _] -> liftM Just $ reduceToWhnf arg
        | op `isCoreBuiltin` The_view ->
            case args of [arg, _] -> liftM Just $ reduceToWhnf arg
        | op `isCoreBuiltin` The_Stream1 -> return_list_dim
        | op `isCoreBuiltin` The_Sequence -> return_list_dim
        | op `isCoreBuiltin` The_list -> return_list_dim
        | op `isCoreBuiltin` The_array0 -> return_dim0
        | op `isCoreBuiltin` The_array1 -> return_dim1
        | op `isCoreBuiltin` The_array2 -> return_dim2
        | op `isCoreBuiltin` The_array3 -> return_dim3
        | op `isCoreBuiltin` The_blist -> return_list_dim
        | op `isCoreBuiltin` The_barray1 -> return_dim1
        | op `isCoreBuiltin` The_barray2 -> return_dim2
        | op `isCoreBuiltin` The_barray3 -> return_dim3
        | op `isCoreBuiltin` The_array ->
            case args
            of [dim, _] -> do
                 dim' <- reduceToWhnf dim
                 case dim' of
                   VarT v | v `isCoreBuiltin` The_dim0 -> return_dim0
                          | v `isCoreBuiltin` The_dim1 -> return_dim1
                          | v `isCoreBuiltin` The_dim2 -> return_dim2
                          | v `isCoreBuiltin` The_dim3 -> return_dim3
                   _ -> return Nothing
        | op `isCoreBuiltin` The_arr ->
            case args
            of [arg, _] -> return $ Just $ array_shape arg
     _ -> return Nothing
  where
    return_list_dim, return_dim0, return_dim1, return_dim2, return_dim3 :: EvalMonad m => m (Maybe Type)
    return_list_dim = return $ Just $ VarT (coreBuiltin The_list_dim)
    return_dim0 = return $ Just $ VarT (coreBuiltin The_dim0)
    return_dim1 = return $ Just $ VarT (coreBuiltin The_dim1)
    return_dim2 = return $ Just $ VarT (coreBuiltin The_dim2)
    return_dim3 = return $ Just $ VarT (coreBuiltin The_dim3)

cartPureTF = typeFunction 1 $ \[index_type] -> do
  index_type' <- reduceToWhnf index_type
  let can't_reduce =
        return $ varApp (coreBuiltin The_cartesianDomain) [index_type]
  case fromVarApp index_type' of
    Just (op, [])
      | op `isCoreBuiltin` The_NoneType -> return_dim0
      | op `isCoreBuiltin` The_int -> return_dim1
    Just (op, [t1, t2])
      | op `isCoreBuiltin` The_Tuple2 ->
          ifM (is_int t1 >&&> is_int t2) return_dim2 can't_reduce
    Just (op, [t1, t2, t3])
      | op `isCoreBuiltin` The_Tuple3 ->
          ifM (is_int t1 >&&> is_int t2 >&&> is_int t3) return_dim3 can't_reduce
    _ -> can't_reduce
  where
    is_int :: EvalMonad m => Type -> m Bool
    is_int ty = do
      ty' <- reduceToWhnf ty
      return $! case ty
                of VarT v -> v `isCoreBuiltin` The_int
                   _      -> False
    return_dim0, return_dim1, return_dim2, return_dim3 :: EvalMonad m => m Type
    return_dim0 = return $ VarT (coreBuiltin The_dim0)
    return_dim1 = return $ VarT (coreBuiltin The_dim1)
    return_dim2 = return $ VarT (coreBuiltin The_dim2)
    return_dim3 = return $ VarT (coreBuiltin The_dim3)

cartMemTF = typeFunction 1 $ \[index_type] -> do
  index_type' <- reduceToWhnf index_type
  let can't_reduce =
        return $ varApp (coreBuiltin The_cartesianDomain) [index_type]
  case fromVarApp index_type' of
    Just (op, [arg_ty])
      | op `isCoreBuiltin` The_Stored -> do
           arg_ty' <- reduceToWhnf arg_ty
           case fromVarApp arg_ty' of
             Just (op, [])
               | op `isCoreBuiltin` The_NoneType -> return_dim0
               | op `isCoreBuiltin` The_int -> return_dim1
             _ -> can't_reduce
    Just (op, [t1, t2])
      | op `isCoreBuiltin` The_Tuple2 ->
          ifM (is_int t1 >&&> is_int t2) return_dim2 can't_reduce
    Just (op, [t1, t2, t3])
      | op `isCoreBuiltin` The_Tuple3 ->
          ifM (is_int t1 >&&> is_int t2 >&&> is_int t3) return_dim3 can't_reduce
    _ -> can't_reduce
  where
    is_int :: EvalMonad m => Type -> m Bool
    is_int ty = do
      ty' <- reduceToWhnf ty
      case fromVarApp ty' of
        Just (op, [arg_ty]) 
          | op `isCoreBuiltin` The_Stored -> do
              arg_ty' <- reduceToWhnf arg_ty
              return $! case arg_ty'
                        of VarT v -> v `isCoreBuiltin` The_int
                           _      -> False
        _ -> return False

    return_dim0, return_dim1, return_dim2 :: EvalMonad m => m Type
    return_dim0 = return $ VarT (coreBuiltin The_dim0)
    return_dim1 = return $ VarT (coreBuiltin The_dim1)
    return_dim2 = return $ VarT (coreBuiltin The_dim2)
    return_dim3 = return $ VarT (coreBuiltin The_dim3)

-- | Compute the shape of a data type in the memory type system
shapeMemTF = shapeLike $ \op args ->
  case ()
  of () | op `isCoreBuiltin` The_Ref ->
          case args
          of [arg] ->
               case fromVarApp arg 
               of Just (op, [arg2, _]) 
                    | op `isCoreBuiltin` The_Stream ->
                        liftM Just $ reduceToWhnf arg2
                    | op `isCoreBuiltin` The_view ->
                        liftM Just $ reduceToWhnf arg2
                  Just (op, [_])
                    | op `isCoreBuiltin` The_Stream1 -> return_list_dim
                    | op `isCoreBuiltin` The_Sequence -> return_list_dim
                  _ -> return Nothing
        | op `isCoreBuiltin` The_list -> return_list_dim
        | op `isCoreBuiltin` The_array0 -> return_dim0
        | op `isCoreBuiltin` The_array1 -> return_dim1
        | op `isCoreBuiltin` The_array2 -> return_dim2
        | op `isCoreBuiltin` The_array3 -> return_dim3
        | op `isCoreBuiltin` The_blist -> return_list_dim
        | op `isCoreBuiltin` The_barray1 -> return_dim1
        | op `isCoreBuiltin` The_barray2 -> return_dim2
        | op `isCoreBuiltin` The_barray3 -> return_dim3
        | op `isCoreBuiltin` The_array ->
            case args
            of [arg, _] -> return $ Just $ array_shape arg
     _ -> return Nothing
  where
    return_list_dim, return_dim0, return_dim1, return_dim2, return_dim3 :: EvalMonad m => m (Maybe Type)
    return_list_dim = return $ Just $ VarT (coreBuiltin The_list_dim)
    return_dim0 = return $ Just $ VarT (coreBuiltin The_dim0)
    return_dim1 = return $ Just $ VarT (coreBuiltin The_dim1)
    return_dim2 = return $ Just $ VarT (coreBuiltin The_dim2)
    return_dim3 = return $ Just $ VarT (coreBuiltin The_dim3)

indexPureTF = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator [shape_arg] = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | op `isCoreBuiltin` The_list_dim -> return int_type
           | op `isCoreBuiltin` The_dim0 -> return none_type
           | op `isCoreBuiltin` The_dim1 -> return int_type
           | op `isCoreBuiltin` The_dim2 -> return int2_type
           | op `isCoreBuiltin` The_dim3 -> return int3_type
        _ -> return $ varApp (coreBuiltin The_index) [shape_arg']

    none_type = VarT (coreBuiltin The_NoneType)
    int_type = VarT (coreBuiltin The_int)
    int2_type = varApp (coreBuiltin The_Tuple2) [int_type, int_type]
    int3_type = varApp (coreBuiltin The_Tuple3) [int_type, int_type, int_type]

indexMemTF = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator [shape_arg] = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | op `isCoreBuiltin` The_list_dim -> return int_type
           | op `isCoreBuiltin` The_dim0 -> return none_type
           | op `isCoreBuiltin` The_dim1 -> return int_type
           | op `isCoreBuiltin` The_dim2 -> return int2_type
           | op `isCoreBuiltin` The_dim3 -> return int3_type
        _ -> return $ varApp (coreBuiltin The_index) [shape_arg']

    compute_eliminator ts =
      internalError "Error in type application when reducing a type function"

    none_type = varApp (coreBuiltin The_Stored) [VarT (coreBuiltin The_NoneType)]
    int_type = varApp (coreBuiltin The_Stored) [VarT (coreBuiltin The_int)]
    int2_type = varApp (coreBuiltin The_Tuple2)
                [int_type, int_type]
    int3_type = varApp (coreBuiltin The_Tuple3)
                [int_type, int_type, int_type]

slicePureTF = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator [shape_arg] = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | op `isCoreBuiltin` The_list_dim -> return slice_type
           | op `isCoreBuiltin` The_dim0 -> return none_type
           | op `isCoreBuiltin` The_dim1 -> return slice_type
           | op `isCoreBuiltin` The_dim2 -> return slice2_type
           | op `isCoreBuiltin` The_dim3 -> return slice3_type
        _ -> return $ varApp (coreBuiltin The_slice) [shape_arg']

    none_type = VarT (coreBuiltin The_NoneType)
    slice_type = VarT (coreBuiltin The_SliceObject)
    slice2_type = varApp (coreBuiltin The_Tuple2)
                  [slice_type, slice_type]
    slice3_type = varApp (coreBuiltin The_Tuple3)
                  [slice_type, slice_type, slice_type]

sliceMemTF = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator [shape_arg] = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | op `isCoreBuiltin` The_list_dim -> return slice_type
           | op `isCoreBuiltin` The_dim0 -> return none_type
           | op `isCoreBuiltin` The_dim1 -> return slice_type
           | op `isCoreBuiltin` The_dim2 -> return slice2_type
           | op `isCoreBuiltin` The_dim3 -> return slice3_type
        _ -> return $ varApp (coreBuiltin The_slice) [shape_arg']

    none_type = varApp (coreBuiltin The_Stored)
                [VarT (coreBuiltin The_NoneType)]
    slice_type = VarT (coreBuiltin The_SliceObject)
    slice2_type = varApp (coreBuiltin The_Tuple2)
                  [slice_type, slice_type]
    slice3_type = varApp (coreBuiltin The_Tuple3)
                  [slice_type, slice_type, slice_type]

{-
viewPureTF = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator (shape_arg : other_args) = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | op `isCoreBuiltin` The_list_dim ->
             return $ varApp (coreBuiltin The_list_view) other_args
           | op `isCoreBuiltin` The_dim0 ->
             return $ varApp (coreBuiltin The_view0) other_args
           | op `isCoreBuiltin` The_dim1 ->
             return $ varApp (coreBuiltin The_view1) other_args
           | op `isCoreBuiltin` The_dim2 ->
             return $ varApp (coreBuiltin The_view2) other_args
        _ -> return $ varApp (coreBuiltin The_view) (shape_arg' : other_args)

viewMemTF = typeFunction 1 compute_eliminator
  where
    compute_eliminator :: forall m. EvalMonad m => [Type] -> m Type
    compute_eliminator (shape_arg : other_args) = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
           | op `isCoreBuiltin` The_list_dim ->
             return $ varApp (coreBuiltin The_list_view) other_args
           | op `isCoreBuiltin` The_dim0 ->
             return $ varApp (coreBuiltin The_view0) other_args
           | op `isCoreBuiltin` The_dim1 ->
             return $ varApp (coreBuiltin The_view1) other_args
           | op `isCoreBuiltin` The_dim2 ->
             return $ varApp (coreBuiltin The_view2) other_args
        _ -> return $ varApp (coreBuiltin The_view) (shape_arg' : other_args)
-}

streamPureTF = typeFunction 1 compute_stream
  where
    compute_stream :: forall m. EvalMonad m => [Type] -> m Type
    compute_stream (shape_arg : other_args) = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
          | op `isCoreBuiltin` The_list_dim ->
            return_con The_Stream1 []
          | op `isCoreBuiltin` The_dim0 ||
            op `isCoreBuiltin` The_dim1 ||
            op `isCoreBuiltin` The_dim2 ||
            op `isCoreBuiltin` The_dim3 ->
              return_con The_view [shape_arg']
        _ -> return_con The_Stream [shape_arg']
      where
        return_con :: forall m. EvalMonad m =>
                      BuiltinThing -> [Type] -> m Type
        return_con con args =
          return $ varApp (coreBuiltin con) (args ++ other_args)

streamMemTF = typeFunction 1 compute_stream
  where
    compute_stream :: forall m. EvalMonad m => [Type] -> m Type
    compute_stream (shape_arg : other_args) = do
      -- Evaluate and inspect the shape argument
      shape_arg' <- reduceToWhnf shape_arg
      case fromVarApp shape_arg' of
        Just (op, args')
          | op `isCoreBuiltin` The_list_dim ->
              return_con The_Stream1 []
          | op `isCoreBuiltin` The_dim0 ||
            op `isCoreBuiltin` The_dim1 ||
            op `isCoreBuiltin` The_dim2 ||
            op `isCoreBuiltin` The_dim3 ->
              return_con The_view [shape_arg']
        _ -> return_con The_Stream [shape_arg']
      where
        return_con :: forall m. EvalMonad m =>
                      BuiltinThing -> [Type] -> m Type
        return_con con args =
          return $ varApp (coreBuiltin con) (args ++ other_args)

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

    compute_boxed args =
      internalError $ "Kind error in application of 'BoxedType' (" ++ show (sep (punctuate (text ",") $ map pprType args)) ++ ")"


    eval :: forall m. EvalMonad m => Type -> m Type
    eval arg =
      case fromVarApp arg
      of Just (op, args')
           | op `isCoreBuiltin` The_BareType ||
             op `isCoreBuiltin` The_Ref ->
               -- BoxedType (BareType t)   =  t
               -- BoxedType (StoredBox t)  =  t
               case args'
               of [arg'] -> reduceToWhnf arg'

           | otherwise -> do
               -- If the argument is a data constructor application, then
               -- use 'Boxed' as the adapter type
               tenv <- getTypeEnv
               case lookupDataType op tenv of
                 Just _ -> return $ varApp (coreBuiltin The_Boxed) [arg]
                 _ -> cannot_reduce
         _ -> cannot_reduce
      where
        cannot_reduce =
          return $ varApp (coreBuiltin The_BoxedType) [arg]
          
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

    compute_bare args =
      internalError $ "Kind error in application of 'BareType' (" ++ show (sep (punctuate (text ",") $ map pprType args)) ++ ")"

    eval :: forall m. EvalMonad m => Type -> m Type
    eval arg =
      case arg
      of FunT {} -> stored_type -- Functions are naturally boxed
         AllT {} -> stored_type -- Forall'd types are naturally boxed
         _ -> case fromVarApp arg
              of Just (op, args')
                   | op `isCoreBuiltin` The_BoxedType ||
                     op `isCoreBuiltin` The_Boxed ->
                       -- BareType (BoxedType t)  =  t
                       -- BareType (Boxed t)      =  t
                       case args'
                       of [arg'] -> reduceToWhnf arg'

                   | op `isCoreBuiltin` The_Stream ->
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
          return $ varApp (coreBuiltin The_Ref) [arg]
        cannot_reduce =
          return $ varApp (coreBuiltin The_BareType) [arg]
