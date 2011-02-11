{-| Code generation of @Repr@ dictionaries.
-}

{-# LANGUAGE FlexibleInstances, FlexibleContexts, TypeSynonymInstances #-}
module SystemF.ReprDict where

import Control.Monad
import Control.Monad.Trans

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
type MkDict m = (ExpM -> m ExpM) -> m ExpM

-- | A 'DictEnv' containing 'MkDict' values
type MkDictEnv m = DictEnv.DictEnv (MkDict m)

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

  getDictEnv :: m (MkDictEnv m)
  getDictEnv = withDictEnv return

  withDictEnv :: (MkDictEnv m -> m a) -> m a
  withDictEnv f = getDictEnv >>= f
  
  localDictEnv :: (MkDictEnv m -> MkDictEnv m) -> m a -> m a

lookupReprDict :: ReprDictMonad m => Type -> m (Maybe (MkDict m))
lookupReprDict ty =
  case ty
  of FunT {} ->
       -- Functions all have the same representation
       return $ Just $ mk_fun_dict ty
     _ -> do
       tenv <- getTypeEnv
       id_supply <- getVarIDs
       denv <- getDictEnv
       liftIO $ DictEnv.lookup id_supply tenv ty denv
  where
    mk_fun_dict ty =
      -- Create a boxed representation object, and pass it to the continuation 
      let op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_Box)
          call = ExpM $ AppE defaultExpInfo op [TypM ty] []
      in ($ call)

-- | Add a dictionary to the environment.  It will be used if it is 
--   needed in the remainder of the computation.
saveReprDict :: ReprDictMonad m => Type -> ExpM -> m a -> m a
saveReprDict dict_type dict_exp m =
  localDictEnv (DictEnv.insert dict_pattern) m
  where
    dict_pattern = DictEnv.monoPattern dict_type ($ dict_exp)

-- | If the pattern binds a representation dictionary, record the dictionary 
--   in the environment so it can be looked up later.
saveReprDictPattern :: ReprDictMonad m => PatM -> m a -> m a
saveReprDictPattern pattern m =
  case pattern
  of MemVarP pat_var (BoxPT ::: ty) _
       | Just repr_type <- get_repr_type ty ->
           saveReprDict repr_type (ExpM $ VarE defaultExpInfo pat_var) m
     _ -> m
  where
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
    Just dict -> dict f
    Nothing -> internalError err_msg 
  where
    err_msg = "withReprDict: Cannot construct dictionary for type:\n" ++
              show (pprType param_type)

createDictEnv :: ReprDictMonad m =>
                 FreshVarM (DictEnv.DictEnv (MkDict m))
createDictEnv = do
  let int_dict = DictEnv.monoPattern (VarT (pyonBuiltin the_int))
                 ($ ExpM $ VarE defaultExpInfo $ pyonBuiltin the_repr_int)
  let float_dict = DictEnv.monoPattern (VarT (pyonBuiltin the_float))
                   ($ ExpM $ VarE defaultExpInfo $ pyonBuiltin the_repr_float)
  repr_dict <- createBoxedDictPattern (pyonBuiltin the_Repr) 1
  boxed_dict <- createBoxedDictPattern (pyonBuiltin the_Boxed) 1
  stream_dict <- createBoxedDictPattern (pyonBuiltin the_Stream) 1
  additive_dict <- createBoxedDictPattern (pyonBuiltin the_AdditiveDict) 1
  multiplicative_dict <- createBoxedDictPattern (pyonBuiltin the_MultiplicativeDict) 1
  tuple2_dict <- DictEnv.pattern2 $ \arg1 arg2 ->
    (varApp (pyonBuiltin the_PyonTuple2) [VarT arg1, VarT arg2],
     createDict_Tuple2 arg1 arg2)
  list_dict <- DictEnv.pattern1 $ \arg ->
    (varApp (pyonBuiltin the_list) [VarT arg],
     createDict_list arg)
  complex_dict <- DictEnv.pattern1 $ \arg ->
    (varApp (pyonBuiltin the_Complex) [VarT arg],
     createDict_complex arg)
  return $ DictEnv.DictEnv [repr_dict, boxed_dict, stream_dict,
                            float_dict, int_dict,
                            list_dict, complex_dict,
                            tuple2_dict, additive_dict, multiplicative_dict]

getParamType v subst =
  case substituteVar v subst
  of Just v -> v
     Nothing -> internalError "getParamType"

-- | Add a dictionary to the environment and pass it to the given computation.
saveAndUseDict :: ReprDictMonad m =>
                  Type -> ExpM -> (ExpM -> m ExpM) -> m ExpM
saveAndUseDict dict_type dict_val k =
  saveReprDict dict_type dict_val $ k dict_val

createDict_Tuple2 param_var1 param_var2 subst use_dict =
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

createDict_list param_var subst use_dict =
  withReprDict param $ \elt_dict ->
  let list_dict = mk_list_dict elt_dict
  in use_dict list_dict
  where
    param = getParamType param_var subst
    oper = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_list)
    mk_list_dict elt_dict =
      ExpM $ AppE defaultExpInfo oper [TypM param] [elt_dict]

createDict_complex param_var subst use_dict =
  withReprDict param $ \elt_dict ->
  let cpx_dict = mk_cpx_dict elt_dict
  in use_dict cpx_dict
  where
    param = getParamType param_var subst
    oper = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_Complex)
    mk_cpx_dict elt_dict =
      ExpM $ AppE defaultExpInfo oper [TypM param] [elt_dict]

-- | Get the representation dictionary for a boxed data type.
--   
--   To get the dictionary, call the @the_repr_Box@ function with
--   boxed data type as its parameter.
createBoxedDictPattern :: ReprDictMonad m =>
                          Var -> Int
                       -> FreshVarM (DictEnv.TypePattern (MkDict m))
createBoxedDictPattern con arity = do
  param_vars <- replicateM arity $ newAnonymousVar TypeLevel
  return $
    DictEnv.pattern param_vars (match_type param_vars) (create_dict param_vars)
  where
    match_type param_vars = varApp con (map VarT param_vars) 

    -- Create a function call expression
    --
    -- > the_repr_Box (con arg1 arg2 ... argN)
    create_dict param_vars subst use_dict = use_dict expr
      where
        param_types = [getParamType v subst | v <- param_vars]
        dict_type = varApp con param_types
        op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_Box)
        expr = ExpM $ AppE defaultExpInfo op [TypM dict_type] []
