{-| Code generation of @Repr@ dictionaries.
-}

{-# LANGUAGE FlexibleInstances, FlexibleContexts, TypeSynonymInstances, 
    Rank2Types #-}
module SystemF.ReprDict where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe

import Common.Error
import Common.Supply
import Builtins.Builtins
import qualified SystemF.DictEnv as DictEnv
import SystemF.Syntax
import SystemF.MemoryIR
import Type.Environment
import Type.Rename
import Type.Type

-- | A @MkDict m@ constructs a dictionary in monad @m2, which is normally
--   an instance of 'ReprDictMonad', and makes the dictionary available over
--   the scope of some computation.
newtype MkDict =
  MkDict {mkDict :: forall m. ReprDictMonad m => (ExpM -> m ExpM) -> m ExpM}

-- | A 'DictEnv' containing 'MkDict' values
type MkDictEnv = DictEnv.DictEnv MkDict

-- | A 'DictEnv' containing indexed integer values
type IntIndexEnv = DictEnv.DictEnv ExpM

-- | A monad that keeps track of representation dictionaries
class (Monad m, MonadIO m, Supplies m VarID) => ReprDictMonad m where
  getVarIDs :: m (Supply VarID)
  getVarIDs = withVarIDs return
  
  withVarIDs :: (Supply VarID -> m a) -> m a
  withVarIDs f = getVarIDs >>= f
  
  getTypeEnv :: m TypeEnv
  getTypeEnv = withTypeEnv return

  withTypeEnv :: (TypeEnv -> m a) -> m a
  withTypeEnv f = getTypeEnv >>= f

  getDictEnv :: m MkDictEnv
  getDictEnv = withDictEnv return

  withDictEnv :: (MkDictEnv -> m a) -> m a
  withDictEnv f = getDictEnv >>= f
  
  getIntIndexEnv :: m IntIndexEnv

  localDictEnv :: (MkDictEnv -> MkDictEnv) -> m a -> m a
  localIntIndexEnv :: (IntIndexEnv -> IntIndexEnv) -> m a -> m a  

instance Supplies m VarID => Supplies (MaybeT m) VarID where
  fresh = lift fresh

instance ReprDictMonad m => ReprDictMonad (MaybeT m) where
  getVarIDs = lift getVarIDs
  withVarIDs f = MaybeT $ withVarIDs (runMaybeT . f)
  getTypeEnv = lift getTypeEnv
  withTypeEnv f = MaybeT $ withTypeEnv (runMaybeT . f)
  getDictEnv = lift getDictEnv 
  withDictEnv f = MaybeT $ withDictEnv (runMaybeT . f)
  getIntIndexEnv = lift getIntIndexEnv
  localDictEnv f (MaybeT m) = MaybeT (localDictEnv f m)
  localIntIndexEnv f (MaybeT m) = MaybeT (localIntIndexEnv f m)

lookupReprDict :: ReprDictMonad m => Type -> m (Maybe MkDict)
lookupReprDict ty =
  case ty
  of FunT {} ->
       -- Functions all have the same representation
       return $ Just $ mk_fun_dict ty
     AnyT {} ->
       -- These values act like referenced objects, but contain nothing
       return $ Just $ mk_any_dict ty
     _ -> do
       tenv <- getTypeEnv
       id_supply <- getVarIDs
       denv <- getDictEnv
       liftIO $ DictEnv.lookup id_supply tenv ty denv
  where
    mk_any_dict ty =
      let op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_EmptyReference)
          call = ExpM $ AppE defaultExpInfo op [TypM ty] []
      in MkDict ($ call)

    mk_fun_dict ty =
      -- Create a boxed representation object, and pass it to the continuation 
      let op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_Box)
          call = ExpM $ AppE defaultExpInfo op [TypM ty] []
      in MkDict ($ call)

-- | Look up the integer value indexed by the given index.  The index must
--   have kind 'intindex'.
lookupIndexedInt :: ReprDictMonad m => Type -> m (Maybe ExpM)
lookupIndexedInt ty = do
  tenv <- getTypeEnv
  id_supply <- getVarIDs
  ienv <- getIntIndexEnv
  liftIO $ DictEnv.lookup id_supply tenv ty ienv

lookupIndexedInt' :: ReprDictMonad m => Type -> m ExpM
lookupIndexedInt' ty = lookupIndexedInt ty >>= check
  where
    check (Just x) = return x
    check Nothing  =
      internalError $
      "lookupIndexedInt: Cannot find integer value for " ++ show (pprType ty)

-- | Add a dictionary to the environment.  It will be used if it is 
--   needed in the remainder of the computation.
saveReprDict :: ReprDictMonad m => Type -> ExpM -> m a -> m a
saveReprDict dict_type dict_exp m =
  localDictEnv (DictEnv.insert dict_pattern) m
  where
    dict_pattern = DictEnv.monoPattern dict_type (MkDict ($ dict_exp))

-- | Add an indexed int to the environment.  It will be used if it is 
--   needed in the remainder of the computation.
saveIndexedInt :: ReprDictMonad m => Type -> ExpM -> m a -> m a
saveIndexedInt dict_type dict_exp m =
  localIntIndexEnv (DictEnv.insert dict_pattern) m
  where
    dict_pattern = DictEnv.monoPattern dict_type dict_exp

-- | If the pattern binds a representation dictionary or int index,
--   record the dictionary 
--   in the environment so it can be looked up later.
saveReprDictPattern :: ReprDictMonad m => PatM -> m a -> m a
saveReprDictPattern pattern m =
  case pattern
  of MemVarP pat_var (BoxPT ::: ty) _
       | Just repr_type <- get_repr_type ty ->
           saveReprDict repr_type (ExpM $ VarE defaultExpInfo pat_var) m
     MemVarP pat_var (ValPT Nothing ::: ty) _
       | Just index <- get_int_index ty ->
           saveIndexedInt index (ExpM $ VarE defaultExpInfo pat_var) m
     _ -> m
  where
    get_int_index ty =
      case fromVarApp ty
      of Just (op, [arg])
           | op `isPyonBuiltin` the_IndexedInt -> Just arg
         _ -> Nothing

    get_repr_type ty = 
      case fromVarApp ty 
      of Just (op, [arg])
           | op `isPyonBuiltin` the_Repr -> Just arg
         _ -> Nothing

-- | Find patterns that bind representation dictionaries, and record them
--   in the environment.
saveReprDictPatterns :: ReprDictMonad m => [PatM] -> m a -> m a
saveReprDictPatterns ps m = foldr saveReprDictPattern m ps

withReprDict :: ReprDictMonad m => Type -> (ExpM -> m ExpM) -> m ExpM
withReprDict param_type f = do
  mdict <- lookupReprDict param_type
  case mdict of
    Just (MkDict dict) -> dict f
    Nothing -> internalError err_msg
  where
    err_msg = "withReprDict: Cannot construct dictionary for type:\n" ++
              show (pprType param_type)

createDictEnv :: FreshVarM (MkDictEnv, IntIndexEnv)
createDictEnv = do
  let int_dict = DictEnv.monoPattern (VarT (pyonBuiltin the_int))
                 (MkDict ($ ExpM $ VarE defaultExpInfo $ pyonBuiltin the_repr_int))
  let float_dict = DictEnv.monoPattern (VarT (pyonBuiltin the_float))
                   (MkDict ($ ExpM $ VarE defaultExpInfo $ pyonBuiltin the_repr_float))
  let efftok_dict = DictEnv.monoPattern (VarT (pyonBuiltin the_EffTok))
                    (MkDict ($ ExpM $ VarE defaultExpInfo $ pyonBuiltin the_repr_EffTok))
  repr_dict <- createBoxedDictPattern (pyonBuiltin the_Repr) 1
  boxed_dict <- createBoxedDictPattern (pyonBuiltin the_Boxed) 1
  stream_dict <- createBoxedDictPattern (pyonBuiltin the_Stream) 2
  additive_dict <- createBoxedDictPattern (pyonBuiltin the_AdditiveDict) 1
  multiplicative_dict <- createBoxedDictPattern (pyonBuiltin the_MultiplicativeDict) 1
  referenced_dict <- DictEnv.pattern1 $ \arg -> 
    (varApp (pyonBuiltin the_Referenced) [VarT arg],
     createDict_referenced arg)
  tuple2_dict <- DictEnv.pattern2 $ \arg1 arg2 ->
    (varApp (pyonBuiltin the_PyonTuple2) [VarT arg1, VarT arg2],
     createDict_Tuple2 arg1 arg2)
  tuple3_dict <- do
    v1 <- newAnonymousVar TypeLevel
    v2 <- newAnonymousVar TypeLevel
    v3 <- newAnonymousVar TypeLevel
    return $ DictEnv.pattern [v1, v2, v3]
      (varApp (pyonBuiltin the_PyonTuple3) [VarT v1, VarT v2, VarT v3])
      (createDict_Tuple3 v1 v2 v3)
  tuple4_dict <- do
    v1 <- newAnonymousVar TypeLevel
    v2 <- newAnonymousVar TypeLevel
    v3 <- newAnonymousVar TypeLevel
    v4 <- newAnonymousVar TypeLevel
    return $ DictEnv.pattern [v1, v2, v3, v4]
      (varApp (pyonBuiltin the_PyonTuple4) [VarT v1, VarT v2, VarT v3, VarT v4])
      (createDict_Tuple4 v1 v2 v3 v4)
  list_dict <- DictEnv.pattern1 $ \arg ->
    (varApp (pyonBuiltin the_list) [VarT arg],
     createDict_list arg)
  complex_dict <- DictEnv.pattern1 $ \arg ->
    (varApp (pyonBuiltin the_Complex) [VarT arg],
     createDict_complex arg)
  array_dict <- DictEnv.pattern2 $ \arg1 arg2 ->
    (varApp (pyonBuiltin the_array) [VarT arg1, VarT arg2],
     createDict_array arg1 arg2)

  let dict_env = DictEnv.DictEnv [repr_dict, boxed_dict,
                                  stream_dict,
                                  float_dict, int_dict, efftok_dict,
                                  list_dict, complex_dict, array_dict,
                                  referenced_dict,
                                  tuple2_dict, tuple3_dict, tuple4_dict,
                                  additive_dict, multiplicative_dict]
      index_env = DictEnv.empty
  return (dict_env, index_env)

getParamType v subst =
  case substituteVar v subst
  of Just v -> v
     Nothing -> internalError "getParamType"

-- | Add a dictionary to the environment and pass it to the given computation.
saveAndUseDict :: ReprDictMonad m =>
                  Type -> ExpM -> (ExpM -> m ExpM) -> m ExpM
saveAndUseDict dict_type dict_val k =
  saveReprDict dict_type dict_val $ k dict_val

createDict_Tuple2 :: Var -> Var -> Substitution -> MkDict
createDict_Tuple2 param_var1 param_var2 subst = MkDict $ \use_dict ->
  withReprDict param1 $ \dict1 ->
  withReprDict param2 $ \dict2 -> do
    tmpvar <- newAnonymousVar ObjectLevel
    let dict_exp = ExpM $ VarE defaultExpInfo tmpvar
    body <- saveAndUseDict data_type dict_exp use_dict
    return $ ExpM $ LetE { expInfo = defaultExpInfo 
                         , expBinder = mk_pat tmpvar
                         , expValue = mk_dict dict1 dict2
                         , expBody = body}
  where
    param1 = getParamType param_var1 subst
    param2 = getParamType param_var2 subst
    
    data_type = varApp (pyonBuiltin the_PyonTuple2) [param1, param2]
    dict_type = varApp (pyonBuiltin the_Repr) [data_type]
    
    -- Construct the local variable pattern
    mk_pat tmpvar =
      memVarP tmpvar (BoxPT ::: dict_type)
    
    -- Construct the dictionary
    mk_dict dict1 dict2 =
      let oper = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_PyonTuple2)
      in ExpM $ AppE defaultExpInfo oper [TypM param1, TypM param2]
         [dict1, dict2]

createDict_Tuple3 :: Var -> Var -> Var -> Substitution -> MkDict
createDict_Tuple3 pv1 pv2 pv3 subst = MkDict $ \use_dict ->
  withReprDict param1 $ \dict1 ->
  withReprDict param2 $ \dict2 ->
  withReprDict param3 $ \dict3 -> do
    tmpvar <- newAnonymousVar ObjectLevel
    let dict_exp = ExpM $ VarE defaultExpInfo tmpvar
    body <- saveAndUseDict data_type dict_exp use_dict
    return $ ExpM $ LetE { expInfo = defaultExpInfo 
                         , expBinder = mk_pat tmpvar
                         , expValue = mk_dict dict1 dict2 dict3
                         , expBody = body}
  where
    param1 = getParamType pv1 subst
    param2 = getParamType pv2 subst
    param3 = getParamType pv3 subst

    data_type = varApp (pyonBuiltin the_PyonTuple3) [param1, param2, param3]
    dict_type = varApp (pyonBuiltin the_Repr) [data_type]
    
    -- Construct the local variable pattern
    mk_pat tmpvar = memVarP tmpvar (BoxPT ::: dict_type)
    
    -- Construct the dictionary
    mk_dict dict1 dict2 dict3 =
      let oper = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_PyonTuple3)
      in ExpM $ AppE defaultExpInfo oper [TypM param1, TypM param2, TypM param3]
         [dict1, dict2, dict3]

createDict_Tuple4 :: Var -> Var -> Var -> Var -> Substitution -> MkDict
createDict_Tuple4 pv1 pv2 pv3 pv4 subst = MkDict $ \use_dict ->
  withReprDict param1 $ \dict1 ->
  withReprDict param2 $ \dict2 ->
  withReprDict param3 $ \dict3 ->
  withReprDict param4 $ \dict4 -> do
    tmpvar <- newAnonymousVar ObjectLevel
    let dict_exp = ExpM $ VarE defaultExpInfo tmpvar
    body <- saveAndUseDict data_type dict_exp use_dict
    return $ ExpM $ LetE { expInfo = defaultExpInfo 
                         , expBinder = mk_pat tmpvar
                         , expValue = mk_dict dict1 dict2 dict3 dict4
                         , expBody = body}
  where
    param1 = getParamType pv1 subst
    param2 = getParamType pv2 subst
    param3 = getParamType pv3 subst
    param4 = getParamType pv4 subst

    data_type = varApp (pyonBuiltin the_PyonTuple4) [param1, param2, param3, param4]
    dict_type = varApp (pyonBuiltin the_Repr) [data_type]
    
    -- Construct the local variable pattern
    mk_pat tmpvar = memVarP tmpvar (BoxPT ::: dict_type)
    
    -- Construct the dictionary
    mk_dict dict1 dict2 dict3 dict4 =
      let oper = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_PyonTuple4)
      in ExpM $ AppE defaultExpInfo oper [TypM param1, TypM param2, TypM param3, TypM param4]
         [dict1, dict2, dict3, dict4]

createDict_list :: Var -> Substitution -> MkDict
createDict_list param_var subst = MkDict $ \use_dict ->
  withReprDict param $ \elt_dict ->
  let list_dict = mk_list_dict elt_dict
  in use_dict list_dict
  where
    param = getParamType param_var subst
    oper = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_list)
    mk_list_dict elt_dict =
      ExpM $ AppE defaultExpInfo oper [TypM param] [elt_dict]

createDict_referenced :: Var -> Substitution -> MkDict
createDict_referenced param_var subst = MkDict $ \use_dict ->
  withReprDict param $ \elt_dict ->
  let dict = ExpM $ AppE defaultExpInfo oper [TypM param] [elt_dict]
  in use_dict dict
  where
    param = getParamType param_var subst
    oper = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_Referenced)

createDict_complex :: Var -> Substitution -> MkDict
createDict_complex param_var subst = MkDict $ \use_dict ->
  withReprDict param $ \elt_dict ->
  let cpx_dict = mk_cpx_dict elt_dict
  in use_dict cpx_dict
  where
    param = getParamType param_var subst
    oper = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_Complex)
    mk_cpx_dict elt_dict =
      ExpM $ AppE defaultExpInfo oper [TypM param] [elt_dict]

createDict_array :: Var -> Var -> Substitution -> MkDict
createDict_array param_var1 param_var2 subst = MkDict $ \use_dict -> do
  withReprDict param2 $ \dict2 -> do
    index <- lookupIndexedInt' param1
    tmpvar <- newAnonymousVar ObjectLevel
    let dict_exp = ExpM $ VarE defaultExpInfo tmpvar
    body <- saveAndUseDict data_type dict_exp use_dict
    return $ ExpM $ LetE { expInfo = defaultExpInfo 
                         , expBinder = mk_pat tmpvar
                         , expValue = mk_dict index dict2
                         , expBody = body}
  where
    param1 = getParamType param_var1 subst
    param2 = getParamType param_var2 subst
    
    data_type = varApp (pyonBuiltin the_array) [param1, param2]
    dict_type = varApp (pyonBuiltin the_Repr) [data_type]
    
    -- Construct the local variable pattern
    mk_pat tmpvar =
      memVarP tmpvar (BoxPT ::: dict_type)
    
    -- Construct the dictionary
    mk_dict index dict2 =
      let oper = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_array)
      in ExpM $ AppE defaultExpInfo oper [TypM param1, TypM param2]
         [index, dict2]

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
    match_type param_vars = varApp con (map VarT param_vars) 

    -- Create a function call expression
    --
    -- > the_repr_Box (con arg1 arg2 ... argN)
    create_dict param_vars subst = MkDict ($ expr)
      where
        param_types = [getParamType v subst | v <- param_vars]
        dict_type = varApp con param_types
        op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_Box)
        expr = ExpM $ AppE defaultExpInfo op [TypM dict_type] []
