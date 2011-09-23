{-| Code generation of @Repr@ dictionaries.
-}

{-# LANGUAGE FlexibleInstances, FlexibleContexts, TypeSynonymInstances, 
    Rank2Types #-}
module SystemF.ReprDict where

import Prelude hiding(mapM)
import Control.Monad hiding(mapM)
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Data.Traversable(mapM)

import Common.Error
import Common.Supply
import Builtins.Builtins
import qualified SystemF.DictEnv as DictEnv
import SystemF.Syntax
import SystemF.MemoryIR
import Type.Environment
import Type.Eval
import Type.Substitute(TypeSubst)
import qualified Type.Substitute as Substitute
import Type.Type

-- | A @MkDict@ constructs a value in a singleton type, such as a
--   type class dictionary or an indexed int.
newtype MkDict =
  MkDict {mkDict :: forall m. ReprDictMonad m => m ExpM}

-- | A dictionary environment for several different data types
data SingletonValueEnv =
  SingletonValueEnv
  { -- | A lookup table of 'Repr' dictionaries
    reprDictEnv :: !(DictEnv.DictEnv MkDict)

    -- | A lookup table of 'Shape' dictionaries
  , shapeDictEnv :: !(DictEnv.DictEnv MkDict)

    -- | A lookup table of 'intindex' dictionaries
  , intIndexEnv :: !(DictEnv.DictEnv MkDict)
  }

modifyReprDictEnv f env@(SingletonValueEnv {reprDictEnv = e}) =
  env {reprDictEnv = f e}

modifyShapeDictEnv f env@(SingletonValueEnv {shapeDictEnv = e}) =
  env {shapeDictEnv = f e}

modifyIntIndexEnv f env@(SingletonValueEnv {intIndexEnv = e}) =
  env {intIndexEnv = f e}

-- | A 'DictEnv' containing dictionary values
type MkDictEnv = DictEnv.DictEnv MkDict

-- | A 'DictEnv' containing finite indexed integer values
type IntIndexEnv = DictEnv.DictEnv MkDict

-- | A monad that keeps track of representation dictionaries
class EvalMonad m => ReprDictMonad m where
  getVarIDs :: m (Supply VarID)
  getVarIDs = withVarIDs return
  
  withVarIDs :: (Supply VarID -> m a) -> m a
  withVarIDs f = getVarIDs >>= f

  withTypeEnv :: (TypeEnv -> m a) -> m a
  withTypeEnv f = getTypeEnv >>= f

  getDictEnv :: m SingletonValueEnv
  getDictEnv = withDictEnv return

  withDictEnv :: (SingletonValueEnv -> m a) -> m a
  withDictEnv f = getDictEnv >>= f

  localDictEnv :: (SingletonValueEnv -> SingletonValueEnv) -> m a -> m a

instance Supplies m VarID => Supplies (MaybeT m) VarID where
  fresh = lift fresh

instance TypeEnvMonad m => TypeEnvMonad (MaybeT m) where
  getTypeEnv = lift getTypeEnv
  assume v t (MaybeT m) = MaybeT $ assume v t m

instance ReprDictMonad m => ReprDictMonad (MaybeT m) where
  getVarIDs = lift getVarIDs
  withVarIDs f = MaybeT $ withVarIDs (runMaybeT . f)
  withTypeEnv f = MaybeT $ withTypeEnv (runMaybeT . f)
  getDictEnv = lift getDictEnv 
  withDictEnv f = MaybeT $ withDictEnv (runMaybeT . f)
  localDictEnv f (MaybeT m) = MaybeT (localDictEnv f m)

instance EvalMonad m => EvalMonad (MaybeT m) where
  liftTypeEvalM m = lift $ liftTypeEvalM m

-- | Lookup the representation dictionary of a bare type
lookupReprDict :: ReprDictMonad m => Type -> m (Maybe MkDict)
lookupReprDict t = lookupReprDict' =<< reduceToWhnf t

lookupReprDict' ty@(AnyT {}) =
  -- These values act like referenced objects, but contain nothing
  return $ Just $ mk_any_dict ty
  where
    mk_any_dict ty =
      let op = ExpM $ VarE defaultExpInfo (pyonBuiltin The_repr_EmptyReference)
          call = ExpM $ AppE defaultExpInfo op [TypM ty] []
      in MkDict (return call)
     
lookupReprDict' ty = withDictEnv (DictEnv.lookup ty . reprDictEnv)

-- | Look up the integer value indexed by the given index.  The index must
--   have kind 'intindex'.
lookupIndexedInt :: ReprDictMonad m => Type -> m (Maybe ExpM)
lookupIndexedInt ty = do
  mk <- withDictEnv (DictEnv.lookup ty . intIndexEnv)
  mapM (\(MkDict m) -> m) mk

lookupIndexedInt' :: ReprDictMonad m => Type -> m ExpM
lookupIndexedInt' ty = lookupIndexedInt ty >>= check
  where
    check (Just x) = return x
    check Nothing  =
      internalError $
      "lookupIndexedInt: Cannot find integer value for " ++ show (pprType ty)

lookupShapeDict :: ReprDictMonad m => Type -> m (Maybe ExpM)
lookupShapeDict ty = do
  mk <- withDictEnv (DictEnv.lookup ty . shapeDictEnv)
  mapM (\(MkDict m) -> m) mk

lookupShapeDict' :: ReprDictMonad m => Type -> m ExpM
lookupShapeDict' ty = lookupShapeDict ty >>= check
  where
    check (Just x) = return x
    check Nothing  =
      internalError $
      "lookupShapeDict: Cannot find shape dictionary for " ++ show (pprType ty)

-- | Add a dictionary to the environment.  It will be used if it is 
--   needed in the remainder of the computation.
saveReprDict :: ReprDictMonad m => Type -> ExpM -> m a -> m a
saveReprDict dict_type dict_exp m =
  localDictEnv (modifyReprDictEnv $ DictEnv.insert dict_pattern) m
  where
    dict_pattern = DictEnv.monoPattern dict_type (MkDict (return dict_exp))

-- | Add a dictionary to the environment.  It will be used if it is 
--   needed in the remainder of the computation.
saveShapeDict :: ReprDictMonad m => Type -> ExpM -> m a -> m a
saveShapeDict dict_type dict_exp m =
  localDictEnv (modifyShapeDictEnv $ DictEnv.insert dict_pattern) m
  where
    dict_pattern = DictEnv.monoPattern dict_type (MkDict (return dict_exp))

-- | Add a finite indexed int to the environment.  It will be used if it is 
--   needed in the remainder of the computation.
saveIndexedInt :: ReprDictMonad m => Type -> ExpM -> m a -> m a
saveIndexedInt dict_type dict_exp m =
  localDictEnv (modifyIntIndexEnv $ DictEnv.insert dict_pattern) m
  where
    dict_pattern = DictEnv.monoPattern dict_type (MkDict $ return dict_exp)

-- | If the pattern binds a representation dictionary or int index,
--   record the dictionary 
--   in the environment so it can be looked up later.
saveReprDictPattern :: ReprDictMonad m => PatM -> m a -> m a
saveReprDictPattern (PatM (pat_var ::: ty) _) m =
  case fromVarApp ty
  of Just (op, [arg])
       | op `isPyonBuiltin` The_Repr -> 
           saveReprDict arg (ExpM $ VarE defaultExpInfo pat_var) m
       | op `isPyonBuiltin` The_ShapeDict -> 
           saveShapeDict arg (ExpM $ VarE defaultExpInfo pat_var) m
       | op `isPyonBuiltin` The_FIInt ->
           saveIndexedInt arg (ExpM $ VarE defaultExpInfo pat_var) m
     _ -> m

-- | Find patterns that bind representation dictionaries, and record them
--   in the environment.
saveReprDictPatterns :: ReprDictMonad m => [PatM] -> m a -> m a
saveReprDictPatterns ps m = foldr saveReprDictPattern m ps

getReprDict :: ReprDictMonad m => Type -> m ExpM
getReprDict param_type = do
  mdict <- lookupReprDict param_type
  case mdict of
    Just (MkDict dict) -> dict
    Nothing -> internalError err_msg
  where
    err_msg = "withReprDict: Cannot construct dictionary for type:\n" ++
              show (pprType param_type)

withReprDict :: ReprDictMonad m => Type -> (ExpM -> m a) -> m a
withReprDict param_type k = do
  dict <- getReprDict param_type
  saveReprDict param_type dict (k dict)

createDictEnv :: FreshVarM SingletonValueEnv
createDictEnv = do
  let int_dict =
        valueDict (pyonBuiltin The_int) (pyonBuiltin The_repr_int)
  let float_dict =
        valueDict (pyonBuiltin The_float) (pyonBuiltin The_repr_float)
  let efftok_dict =
        valueDict (pyonBuiltin The_EffTok) (pyonBuiltin The_repr_EffTok)
      sliceobj_dict =
        DictEnv.monoPattern (VarT $ pyonBuiltin The_SliceObject)
        (MkDict $ return $ ExpM $ VarE defaultExpInfo (pyonBuiltin The_repr_SliceObject))
  repr_dict <- createBoxedDictPattern (pyonBuiltin The_Repr) 1
  stream_dict <- createBoxedDictPattern (pyonBuiltin The_Stream) 2
  eq_dict <- createBoxedDictPattern (pyonBuiltin The_EqDict) 1
  ord_dict <- createBoxedDictPattern (pyonBuiltin The_OrdDict) 1
  additive_dict <- createBoxedDictPattern (pyonBuiltin The_AdditiveDict) 1
  multiplicative_dict <- createBoxedDictPattern (pyonBuiltin The_MultiplicativeDict) 1
  referenced_dict <- DictEnv.pattern1 $ \arg -> 
    (varApp (pyonBuiltin The_Referenced) [VarT arg],
     createDict_referenced arg)
  maybe_dict <- DictEnv.pattern1 $ \arg ->
    (varApp (pyonBuiltin The_Maybe) [VarT arg],
     createDict_Maybe arg)
  tuple2_dict <- DictEnv.pattern2 $ \arg1 arg2 ->
    (varApp (pyonBuiltin The_PyonTuple2) [VarT arg1, VarT arg2],
     createDict_Tuple2 arg1 arg2)
  tuple3_dict <- do
    v1 <- newAnonymousVar TypeLevel
    v2 <- newAnonymousVar TypeLevel
    v3 <- newAnonymousVar TypeLevel
    return $ DictEnv.pattern [v1, v2, v3]
      (varApp (pyonBuiltin The_PyonTuple3) [VarT v1, VarT v2, VarT v3])
      (createDict_Tuple3 v1 v2 v3)
  tuple4_dict <- do
    v1 <- newAnonymousVar TypeLevel
    v2 <- newAnonymousVar TypeLevel
    v3 <- newAnonymousVar TypeLevel
    v4 <- newAnonymousVar TypeLevel
    return $ DictEnv.pattern [v1, v2, v3, v4]
      (varApp (pyonBuiltin The_PyonTuple4) [VarT v1, VarT v2, VarT v3, VarT v4])
      (createDict_Tuple4 v1 v2 v3 v4)
  list_dict <- DictEnv.pattern1 $ \arg ->
    (varApp (pyonBuiltin The_list) [VarT arg],
     createDict_list arg)
  complex_dict <- DictEnv.pattern1 $ \arg ->
    (varApp (pyonBuiltin The_Complex) [VarT arg],
     createDict_complex arg)
  array_dict <- DictEnv.pattern2 $ \arg1 arg2 ->
    (varApp (pyonBuiltin The_arr) [VarT arg1, VarT arg2],
     createDict_array arg1 arg2)
  storedBox_dict <- DictEnv.pattern1 $ \arg ->
    (varApp (pyonBuiltin The_StoredBox) [VarT arg],
     createDict_storedBox arg)
  
  index_dict <- DictEnv.pattern1 $ \arg ->
    (varApp (pyonBuiltin The_index) [VarT arg],
     createDict_index arg)
  slice_dict <- DictEnv.pattern1 $ \arg ->
    (varApp (pyonBuiltin The_slice) [VarT arg],
     createDict_slice arg)

  let dict_env = DictEnv.DictEnv [repr_dict, storedBox_dict,
                                  stream_dict,
                                  float_dict, int_dict, efftok_dict,
                                  sliceobj_dict,
                                  list_dict, complex_dict, array_dict,
                                  referenced_dict, maybe_dict,
                                  tuple2_dict, tuple3_dict, tuple4_dict,
                                  eq_dict, ord_dict,
                                  additive_dict, multiplicative_dict,
                                  index_dict, slice_dict]
      
  minimum_int <- DictEnv.pattern2 $ \arg1 arg2 ->
    (varApp (pyonBuiltin The_min_i) [VarT arg1, VarT arg2],
     createInt_min arg1 arg2)
  minus_int <- DictEnv.pattern2 $ \arg1 arg2 ->
    (varApp (pyonBuiltin The_minus_i) [VarT arg1, VarT arg2],
     createInt_minus arg1 arg2)
  let index_env = DictEnv.DictEnv [minimum_int, minus_int]

  return $ SingletonValueEnv { reprDictEnv = dict_env
                             , shapeDictEnv = DictEnv.DictEnv []
                             , intIndexEnv = index_env
                             }

getParamType v subst =
  case Substitute.lookup v subst
  of Just v -> v
     Nothing -> internalError "getParamType"

-- | Create a dictionary for a monomorphic value type.
valueDict :: Var -> Var -> DictEnv.TypePattern MkDict
valueDict value_var dict_var =
  DictEnv.monoPattern pattern_type expr
  where
    pattern_type = varApp (pyonBuiltin The_Stored) [VarT value_var]
    expr = MkDict $ return $ ExpM $ VarE defaultExpInfo dict_var

createDict_Tuple2 :: Var -> Var -> TypeSubst -> MkDict
createDict_Tuple2 param_var1 param_var2 subst = MkDict $
  withReprDict param1 $ \dict1 ->
  withReprDict param2 $ \dict2 ->
  return $ ExpM $ AppE defaultExpInfo dict_oper [TypM param1, TypM param2]
  [dict1, dict2]
  where
    param1 = getParamType param_var1 subst
    param2 = getParamType param_var2 subst
    
    data_type = varApp (pyonBuiltin The_PyonTuple2) [param1, param2]
    dict_type = varApp (pyonBuiltin The_Repr) [data_type]
    dict_oper = ExpM $ VarE defaultExpInfo (pyonBuiltin The_repr_PyonTuple2)

createDict_Tuple3 :: Var -> Var -> Var -> TypeSubst -> MkDict
createDict_Tuple3 pv1 pv2 pv3 subst = MkDict $
  withReprDict param1 $ \dict1 ->
  withReprDict param2 $ \dict2 ->
  withReprDict param3 $ \dict3 ->
  return $ ExpM $ AppE defaultExpInfo dict_oper
      [TypM param1, TypM param2, TypM param3]
      [dict1, dict2, dict3]
  where
    param1 = getParamType pv1 subst
    param2 = getParamType pv2 subst
    param3 = getParamType pv3 subst

    data_type = varApp (pyonBuiltin The_PyonTuple3) [param1, param2, param3]
    dict_type = varApp (pyonBuiltin The_Repr) [data_type]
    dict_oper = ExpM $ VarE defaultExpInfo (pyonBuiltin The_repr_PyonTuple3)

createDict_Tuple4 :: Var -> Var -> Var -> Var -> TypeSubst -> MkDict
createDict_Tuple4 pv1 pv2 pv3 pv4 subst = MkDict $
  withReprDict param1 $ \dict1 ->
  withReprDict param2 $ \dict2 ->
  withReprDict param3 $ \dict3 ->
  withReprDict param4 $ \dict4 ->
  return $ ExpM $ AppE defaultExpInfo dict_oper
      [TypM param1, TypM param2, TypM param3, TypM param4]
      [dict1, dict2, dict3, dict4]
  where
    param1 = getParamType pv1 subst
    param2 = getParamType pv2 subst
    param3 = getParamType pv3 subst
    param4 = getParamType pv4 subst

    data_type = varApp (pyonBuiltin The_PyonTuple4) [param1, param2, param3, param4]
    dict_type = varApp (pyonBuiltin The_Repr) [data_type]
    dict_oper = ExpM $ VarE defaultExpInfo (pyonBuiltin The_repr_PyonTuple4)

createDict_list :: Var -> TypeSubst -> MkDict
createDict_list param_var subst = MkDict $
  withReprDict param $ \elt_dict ->
  return $ ExpM $ AppE defaultExpInfo oper [TypM param] [elt_dict]
  where
    param = getParamType param_var subst
    oper = ExpM $ VarE defaultExpInfo (pyonBuiltin The_repr_list)

createDict_referenced :: Var -> TypeSubst -> MkDict
createDict_referenced param_var subst = MkDict $
  withReprDict param $ \elt_dict ->
  return $ ExpM $ AppE defaultExpInfo oper [TypM param] [elt_dict]
  where
    param = getParamType param_var subst
    oper = ExpM $ VarE defaultExpInfo (pyonBuiltin The_repr_Referenced)

createDict_Maybe :: Var -> TypeSubst -> MkDict
createDict_Maybe param_var subst = MkDict $
  withReprDict param $ \elt_dict ->
  return $ ExpM $ AppE defaultExpInfo oper [TypM param] [elt_dict]
  where
    param = getParamType param_var subst
    oper = ExpM $ VarE defaultExpInfo (pyonBuiltin The_repr_Maybe)

createDict_complex :: Var -> TypeSubst -> MkDict
createDict_complex param_var subst = MkDict $
  withReprDict param $ \elt_dict ->
  return $ ExpM $ AppE defaultExpInfo oper [TypM param] [elt_dict]
  where
    param = getParamType param_var subst
    oper = ExpM $ VarE defaultExpInfo (pyonBuiltin The_repr_Complex)

createDict_array :: Var -> Var -> TypeSubst -> MkDict
createDict_array param_var1 param_var2 subst = MkDict $
  withReprDict param2 $ \dict2 -> do
    index <- lookupIndexedInt' param1
    return $ ExpM $ AppE defaultExpInfo oper [TypM param1, TypM param2]
      [index, dict2]
  where
    param1 = getParamType param_var1 subst
    param2 = getParamType param_var2 subst
    
    data_type = varApp (pyonBuiltin The_arr) [param1, param2]
    dict_type = varApp (pyonBuiltin The_Repr) [data_type]
    oper = ExpM $ VarE defaultExpInfo (pyonBuiltin The_repr_arr)

createDict_storedBox :: Var -> TypeSubst -> MkDict
createDict_storedBox param_var subst = MkDict $ do
  return $ ExpM $ AppE defaultExpInfo oper [TypM param] []
  where
    param = getParamType param_var subst
    oper = ExpM $ VarE defaultExpInfo (pyonBuiltin The_repr_Box)

-- | Get the representation dictionary for a boxed data type.
--   
--   To get the dictionary, call the @the_repr_Box@ function with
--   boxed data type as its parameter.
createBoxedDictPattern :: Var -> Int -> FreshVarM (DictEnv.TypePattern MkDict)
createBoxedDictPattern con arity = do
  param_vars <- replicateM arity $ newAnonymousVar TypeLevel
  return $
    DictEnv.pattern param_vars (match_type param_vars) (create_dict param_vars)
  where
    match_type param_vars =
      varApp (pyonBuiltin The_StoredBox) [varApp con (map VarT param_vars)]

    -- Create a function call expression
    --
    -- > the_repr_Box (con arg1 arg2 ... argN)
    create_dict param_vars subst = MkDict (return expr)
      where
        param_types = [getParamType v subst | v <- param_vars]
        dict_type = varApp con param_types
        op = ExpM $ VarE defaultExpInfo (pyonBuiltin The_repr_Box)
        expr = ExpM $ AppE defaultExpInfo op [TypM dict_type] []

createDict_index param_var subst = MkDict $ do
  -- The Repr object for an @index sh@ is stored in the @ShapeDict sh@.  
  -- Look it up in the shape dictionary if it's not in the environment.
  shape_dict <- lookupShapeDict' param
  return $ ExpM $ AppE defaultExpInfo oper [TypM param] [shape_dict]
  where
    param = getParamType param_var subst
    oper = ExpM $ VarE defaultExpInfo (pyonBuiltin The_shapeIndexRepr)
  
createDict_slice param_var subst = MkDict $ do
  -- The Repr object for a @slice sh@ is stored in the @ShapeDict sh@.  
  -- Look it up in the shape dictionary if it's not in the environment.
  shape_dict <- lookupShapeDict' param
  return $ ExpM $ AppE defaultExpInfo oper [TypM param] [shape_dict]
  where
    param = getParamType param_var subst
    oper = ExpM $ VarE defaultExpInfo (pyonBuiltin The_shapeSliceRepr)

createInt_min param_var1 param_var2 subst = MkDict $ do
  int1 <- lookupIndexedInt' param1
  int2 <- lookupIndexedInt' param2
  return $ ExpM $
    AppE defaultExpInfo oper [TypM param1, TypM param2] [int1, int2]
  where
    param1 = getParamType param_var1 subst
    param2 = getParamType param_var2 subst

    oper = ExpM $ VarE defaultExpInfo (pyonBuiltin The_min_ii)

createInt_minus param_var1 param_var2 subst = MkDict $ do
  int1 <- lookupIndexedInt' param1
  int2 <- lookupIndexedInt' param2
  return $ ExpM $
    AppE defaultExpInfo oper [TypM param1, TypM param2] [int1, int2]
  where
    param1 = getParamType param_var1 subst
    param2 = getParamType param_var2 subst

    oper = ExpM $ VarE defaultExpInfo (pyonBuiltin The_minus_ii)
