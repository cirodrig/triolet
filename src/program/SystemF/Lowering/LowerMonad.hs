
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances,
    GeneralizedNewtypeDeriving, Rank2Types #-}
module SystemF.Lowering.LowerMonad where

import Control.Applicative
import Control.Monad 
import Control.Monad.Trans  
import Control.Monad.Reader
import Control.Monad.ST
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Set as Set

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.Supply
import Builtins.Builtins
import LowLevel.Build
import qualified LowLevel.Records as LL
import qualified LowLevel.Builtins as LL
import qualified LowLevel.Syntax as LL
import qualified LowLevel.CodeTypes as LL
import SystemF.Datatypes.Util
import SystemF.Datatypes.Size
import SystemF.Syntax
import Type.Environment
import Type.Eval
import Type.Type
import Type.Substitute(TypeSubst)
import qualified Type.Substitute as Substitute

-- | A low-level translation of a variable.
--
--   Most core variables translate to low-level variables.
--   However, some global constants are
--   translated to lazy evaluation of global functions.
data VarTranslation =
    -- | An ordinary variable
    Variable !LL.Var

    -- | A lazily evaluated object.
    --   The kind and low-level type of the lazy variable's value are included
    --   here.  The variable is a lazy object.
  | Lazy !BaseKind !LL.ValueType !LL.Var

-- | Get the translated variable from a 'VarTranslation'.
--   Because there are different ways of translating a core variable to a
--   low-level one, the translated variable may not be a drop-in replacement
--   for the original variable.
translatedVar :: VarTranslation -> LL.Var
translatedVar (Variable v) = v
translatedVar (Lazy _ _ v) = v

newtype Lower a = Lower (ReaderT LowerEnv UnboxedTypeEvalM a)
                deriving(Functor, Applicative, Monad, MonadIO)

runLowering :: LowerEnv -> Lower a -> UnboxedTypeEvalM a
runLowering env (Lower m) = runReaderT m env

type GenLower a = Gen Lower a

data LowerEnv =
  LowerEnv { llVarSupply :: {-# UNPACK #-}!(IdentSupply LL.Var)

             -- | Each in-scope variable is associated with a
             --   low-level variable or expression
           , varMap :: !(IntMap.IntMap VarTranslation)
           
             -- | Pre-defined variables are kept in this map as well as
             --   in 'varMap'
           , predefinedVarMap :: !(IntMap.IntMap VarTranslation)
           }

getLLVarSupply :: Lower (IdentSupply LL.Var)
getLLVarSupply = Lower $ asks llVarSupply

getVarSupply :: Lower (IdentSupply Var)
getVarSupply = Lower $ lift $ TypeEvalM $ \s _ -> return s

getTypeEnvironment :: Lower TypeEnv
getTypeEnvironment = Lower $ lift getTypeEnv

initializeLowerEnv :: IdentSupply LL.Var
                   -> Map.Map Var LL.Var
                   -> IO LowerEnv
initializeLowerEnv var_supply var_map =
  return $ LowerEnv var_supply global_map global_map
  where
    global_map = IntMap.fromList [(fromIdent $ varID v, Variable v')
                                 | (v, v') <- Map.toList var_map]

instance Supplies Lower (Ident Var) where
  fresh = Lower $ lift fresh
  supplyToST f = Lower $ lift (supplyToST f)

instance Supplies Lower (Ident LL.Var) where
  fresh = Lower $ ReaderT $ \env -> liftIO $ supplyValue $ llVarSupply env

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
  type EvalBoxingMode Lower = UnboxedMode
  getTypeEnv = Lower $ lift getTypeEnv
  liftTypeEnvM m = Lower $ lift $ liftTypeEnvM m

instance EvalMonad Lower where
  liftTypeEvalM m = Lower $ lift m

isPredefinedVar :: Var -> Lower Bool
isPredefinedVar v = Lower $ ReaderT $ \env ->
  return $ (fromIdent $ varID v) `IntMap.member` predefinedVarMap env

lookupVar :: Var -> Lower VarTranslation
lookupVar v = Lower $ ReaderT $ \env ->
  case IntMap.lookup (fromIdent $ varID v) $ varMap env
  of Just vt -> return vt
     Nothing -> internalError $
                "Lowering: no translation for variable: " ++ show v

-- | Create a new low-level variable to stand for the given variable 
translateVariable :: Bool -> Var -> Type -> Lower LL.Var
translateVariable is_external v sf_ty = do
  ty <- lowerLowerType sf_ty
  translateVariableWithType is_external v ty

-- | Create a new low-level lazy variable to stand for the given variable 
translateLazyVariable :: Bool -> Var -> Lower LL.Var
translateLazyVariable is_external v =
  translateVariableWithType is_external v (LL.PrimType LL.PointerType)

translateVariableWithType True v ty =
  case varName v
  of Just nm -> LL.newExternalVar nm ty
     Nothing -> internalError $ 
                "translateVariableWithType: Exported variable must have label"
                
translateVariableWithType False v ty =
  LL.newVar (varName v) ty

assumeTranslatedVariable :: Var -> VarTranslation -> Type -> Lower a -> Lower a
assumeTranslatedVariable v new_v sf_ty (Lower m) =
  assume v sf_ty (Lower (local update m))
  where
    update env =
      env {varMap = IntMap.insert (fromIdent $ varID v) new_v $ varMap env}

-- | Perform some computation that also generates code; emit the code
lowerAndGenerateCode :: GenM a -> GenLower a
lowerAndGenerateCode g = Gen $ \return_types ->
  Lower $ ReaderT $ \env -> do
    (x, mk_stm) <- runGenM' (llVarSupply env) return_types g
    return (x, mk_stm)

-- | Perform some computation that must not generate code
lowerAndGenerateNothing :: GenM a -> Lower a
lowerAndGenerateNothing g = Lower $ ReaderT $ \env ->
  runGenMWithoutOutput (llVarSupply env) g

-- | Convert a @GenLower a@ to a @GenM a@.  The variable mapping is saved
--   for later use.
embedIntoGenM :: (a -> GenLower b) -> GenLower (a -> GenM b)
embedIntoGenM f = do
  -- Get the current variable maps
  env <- lift $ Lower ask
  let var_map = varMap env
      predefined_var_map = predefinedVarMap env
  return $ \x -> Gen $ \rt -> SizeComputing $ ReaderT $ \var_supply ->
    let lower_env = LowerEnv var_supply var_map predefined_var_map
    in runLowering lower_env (runGen (f x) rt)
    
lowerLowerType :: Type -> Lower LL.ValueType
lowerLowerType ty = Lower $ ReaderT $ \env -> do
  lowerType (llVarSupply env) ty

