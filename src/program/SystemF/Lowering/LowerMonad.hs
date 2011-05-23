
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances,
    GeneralizedNewtypeDeriving, Rank2Types #-}
module SystemF.Lowering.LowerMonad where

import Control.Monad 
import Control.Monad.Trans  
import Control.Monad.Reader
import Control.Monad.ST
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.Supply
import Builtins.Builtins
import LowLevel.Build
import qualified LowLevel.Builtins as LL
import qualified LowLevel.Syntax as LL
import qualified LowLevel.CodeTypes as LL
import qualified SystemF.DictEnv as DictEnv
import SystemF.Syntax
import Type.Environment
import Type.Type
import Type.Rename

newtype Lower a = Lower (ReaderT LowerEnv IO a)
                deriving(Functor, Monad, MonadIO)

runLowering :: LowerEnv -> Lower a -> IO a
runLowering env (Lower m) = runReaderT m env

liftFreshVarM :: FreshVarM a -> Lower a
liftFreshVarM m = Lower $ ReaderT $ \env -> runFreshVarM (varSupply env) m

type GenLower a = Gen Lower a

data LowerEnv =
  LowerEnv { varSupply :: {-# UNPACK #-}!(IdentSupply Var)
           , llVarSupply :: {-# UNPACK #-}!(IdentSupply LL.Var)
           , typeEnvironment :: !TypeEnv
             
             -- | The type-indexed integers in the environment.
             --   Indexed by the type index.
           , intEnvironment :: DictEnv.DictEnv LL.Val

             -- | The 'Repr' dictionaries in the environment.  Indexed
             --   by the dictionary's type parameter.
           , reprDictEnvironment :: DictEnv.DictEnv (GenLower LL.Val)

             -- | A low-level variable is associated to each variable that
             --   is in scope
           , varMap :: IntMap.IntMap LL.Var
           }

initializeLowerEnv :: IdentSupply Var
                   -> IdentSupply LL.Var
                   -> TypeEnv
                   -> Map.Map Var LL.Var
                   -> IO LowerEnv
initializeLowerEnv var_supply ll_var_supply type_env var_map = do
  repr_env <- runFreshVarM var_supply $ mk_repr_env
  let global_map = IntMap.fromList [(fromIdent $ varID v, v')
                                   | (v, v') <- Map.toList var_map]
      int_env = DictEnv.empty
  return $ LowerEnv var_supply ll_var_supply type_env int_env repr_env global_map
  where
    -- Populate the environment with globally defined Repr instances
    mk_repr_env = do 
      repr_dict <- DictEnv.pattern1 $ \arg ->
        (varApp (pyonBuiltin the_Repr) [VarT arg], mk_repr_dict arg)
      let int_dict =
            mono_dict (VarT $ pyonBuiltin the_int) LL.the_bivar_repr_int
      let float_dict =
            mono_dict (VarT $ pyonBuiltin the_float) LL.the_bivar_repr_float
      additive_dict <- DictEnv.pattern1 $ \arg ->
        (varApp (pyonBuiltin the_AdditiveDict) [VarT arg],
         mk_additive_dict arg)
      multiplicative_dict <- DictEnv.pattern1 $ \arg ->
        (varApp (pyonBuiltin the_MultiplicativeDict) [VarT arg],
         mk_multiplicative_dict arg)
      (tuple2_dict, tuple3_dict, tuple4_dict) <- do
        v1 <- newAnonymousVar TypeLevel
        v2 <- newAnonymousVar TypeLevel
        v3 <- newAnonymousVar TypeLevel
        v4 <- newAnonymousVar TypeLevel
        let ty2 = varApp (pyonBuiltin the_PyonTuple2)
                  [VarT v1, VarT v2]
        let ty3 = varApp (pyonBuiltin the_PyonTuple3)
                  [VarT v1, VarT v2, VarT v3]
        let ty4 = varApp (pyonBuiltin the_PyonTuple4)
                  [VarT v1, VarT v2, VarT v3, VarT v4]
        return (DictEnv.pattern [v1, v2] ty2 (mk_tuple_dict [v1, v2]),
                DictEnv.pattern [v1, v2, v3] ty3 (mk_tuple_dict [v1, v2, v3]),
                DictEnv.pattern [v1, v2, v3, v4] ty4 (mk_tuple_dict [v1, v2, v3]))
      return $ DictEnv.DictEnv [float_dict, int_dict, repr_dict,
                                additive_dict, multiplicative_dict,
                                tuple2_dict, tuple3_dict, tuple4_dict]

    mono_dict ty val =
      DictEnv.monoPattern ty (return (LL.VarV $ LL.llBuiltin val))

    -- Need a (Repr a) to create a (Repr (AdditiveDict a))
    mk_additive_dict arg = \subst -> undefined

    -- Need a (Repr a) to create a (Repr (MultiplicativeDict a))
    mk_multiplicative_dict arg = \subst -> undefined

    -- Get a representation dictionary for (Repr a)
    mk_repr_dict _ _ = return repr_Box_value

    -- This is the representation dictionary for Repr objects
    repr_Box_value = LL.VarV $ LL.llBuiltin LL.the_bivar_repr_Box_value
    
    mk_tuple_dict :: [Var] -> Substitution -> GenLower LL.Val
    mk_tuple_dict args = \subst -> do
      -- Get repr dictionaries for each type argument
      withMany (with_arg_dict subst) args $ \arg_dicts -> do
        -- Pick the correct function
        let op = tuple_dict_constructor (length arg_dicts)
            
        -- Call the constructor function
        emitAtom1 (LL.PrimType LL.OwnedType) $
          LL.closureCallA (LL.VarV op) arg_dicts
      
      where
        with_arg_dict subst arg k =
          let arg' = case substituteVar arg subst
                     of Just t -> t
                        Nothing -> internalError "initializeLowerEnv"
          in lookupReprDict arg' k
    
    tuple_dict_constructor 2 = LL.llBuiltin LL.the_fun_repr_PyonTuple2
    tuple_dict_constructor 3 = LL.llBuiltin LL.the_fun_repr_PyonTuple3
    tuple_dict_constructor 4 = LL.llBuiltin LL.the_fun_repr_PyonTuple4

instance Supplies Lower (Ident Var) where
  fresh = Lower $ ReaderT $ \env -> supplyValue $ varSupply env
  supplyToST f = Lower $ ReaderT $ \env ->
    let get_fresh = unsafeIOToST $ supplyValue (varSupply env)
    in stToIO (f get_fresh)

instance Supplies Lower (Ident LL.Var) where
  fresh = Lower $ ReaderT $ \env -> supplyValue $ llVarSupply env

liftT :: (forall b. Lower b -> Lower b) -> GenLower a -> GenLower a
liftT t m = do
  rt <- getReturnTypes
  (g, x) <- lift $ t $ suspendGen rt m
  g
  return x

liftT1 :: (forall b. (c -> Lower b) -> Lower b)
       -> (c -> GenLower a) -> GenLower a
liftT1 t k = do
  rt <- getReturnTypes
  (g, x) <- lift $ t $ \arg -> suspendGen rt (k arg)
  g
  return x

instance TypeEnvMonad Lower where
  getTypeEnv = Lower $ asks typeEnvironment
  
  assume v t (Lower m) = Lower $ local update m
    where
      update env =
        env {typeEnvironment = insertType v t $ typeEnvironment env}

instance EvalMonad Lower

-- | Find the Repr dictionary for the given type, which should be a type
--   variable.  Fail if not found.
lookupReprDict :: Type -> (LL.Val -> GenLower a) -> GenLower a
lookupReprDict ty k = do
  match <- lift lookup_dict
  case match of
    Just dict_val -> k =<< dict_val
    Nothing -> internalError $ 
               "lookupReprDict: Dictionary not found for type:\n" ++ show (pprType ty)
  where
    lookup_dict = do
      dict_env <- Lower $ asks reprDictEnvironment  
      DictEnv.lookup ty dict_env

-- | Add a Repr dictionary for this type to the environment
assumeReprDict :: Type -> LL.Val -> Lower a -> Lower a
assumeReprDict ty val (Lower m) = Lower $ local update m
  where
    update env = env {reprDictEnvironment =
                         DictEnv.insert (DictEnv.monoPattern ty (return val)) $
                         reprDictEnvironment env}

-- | Find an integer indexed by the given index, which should be a type
--   of kind @intindex@.  Fail if not found.
lookupIndexedInt :: Type -> Lower LL.Val
lookupIndexedInt ty = do
  match <- lookup_dict
  case match of
    Just int_val -> return int_val
    Nothing -> internalError $ 
               "lookupIndexedInt: Not found for index:\n" ++ show (pprType ty)
  where
    lookup_dict = do
      dict_env <- Lower $ asks intEnvironment  
      DictEnv.lookup ty dict_env

-- | Add an indexed integer for this type index to the environment
assumeIndexedInt :: Type -> LL.Val -> Lower a -> Lower a
assumeIndexedInt ty val (Lower m) = Lower $ local update m
  where
    update env = env {intEnvironment =
                         DictEnv.insert (DictEnv.monoPattern ty val) $
                         intEnvironment env}

lookupVar :: Var -> Lower LL.Var
lookupVar v = Lower $ ReaderT $ \env ->
  case IntMap.lookup (fromIdent $ varID v) $ varMap env
  of Just ll_var -> return ll_var
     Nothing -> internalError $
                "Lowering: no translation for variable: " ++ show v

assumeVariableWithType :: Var -> LL.ValueType -> (LL.Var -> Lower a) -> Lower a
assumeVariableWithType v ty k = do
  new_v <- LL.newVar (varName v) ty
  add_to_env new_v (k new_v)
  where  
    add_to_env new_v (Lower m) = Lower $ local update m
      where
        update env = env {varMap = IntMap.insert (fromIdent $ varID v) new_v $ 
                                   varMap env}

-- | Add a type variable to the type environment
assumeType :: Var -> Type -> Lower a -> Lower a
assumeType v kind m
  | getLevel v /= TypeLevel = internalError "assumeType: Not a type variable"
  | getLevel kind /= KindLevel = internalError "assumeType: Not a kind"
  | otherwise = assume v kind m
