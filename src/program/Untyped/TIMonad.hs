
module Untyped.TIMonad where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.RWS
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.IORef
import System.IO.Unsafe
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import qualified Type.Type as SF
import Untyped.Kind
import Untyped.Type
import Untyped.TIExp
import Untyped.Unif
import Untyped.Variable

theTyVarIDSupply :: IdentSupply TyVar
{-# NOINLINE theTyVarIDSupply #-}
theTyVarIDSupply = unsafePerformIO newUVarIDSupply

freshTyVarID :: IO (Ident TyVar)
freshTyVarID = supplyValue theTyVarIDSupply

-- | Type information assigned to a type variable.
--
--   The kind and System F equivalent are stored in the variable itself.
data TypeBinding =
    TyVarAss                    -- ^ A non-unifiable type variable
  | TyConAss !DataType          -- ^ A type constructor.  The flag is true iff
                                --   the constructed type is boxed.
  | TyClsAss !Class             -- ^ A type class
  | TyFunAss !TyFamily          -- ^ A type family

data ValueBinding =
    PolyVarAss TyScheme          -- ^ A polymorphic variable
  | MonoVarAss HMType            -- ^ A monomorphic variable
  | RecVarAss RecVarInfo         -- ^ A recursive variable whose value is
                                 --   given by the placeholder
  | DataConAss !DataCon          -- ^ A data constructor
  | MethodAss TyCon !Int         -- ^ A class method, given as a class and
                                 --   a method index.

data Environment =
  Environment
  { envTypes :: Map.Map TyCon TypeBinding
  , envValues :: Map.Map Variable ValueBinding
  , envSFVarIDSupply :: {-# UNPACK #-}!(IdentSupply SF.Var)
  }

insertValueBinding :: Variable -> ValueBinding -> Environment -> Environment
insertValueBinding v b env = env {envValues = Map.insert v b $ envValues env}

insertTypeBinding :: TyCon -> TypeBinding -> Environment -> Environment
insertTypeBinding v b env = env {envTypes = Map.insert v b $ envTypes env}

-- | Placeholders for a recursive variable's type and value.
--
--   Placeholders are created for a recursive variable to stand for the 
--   variable's monomorphic type and value within a recursive definition 
--   group.
data RecVarInfo =
  RecVarInfo
  { recVarType :: !TyVar        -- ^ A unifiable type variable standing for
                                --   the variable's type
  , recVarValue :: !RecVarP     -- ^ A placeholder standing for the variable's
                                --   value
  }

-- | Look up a type constructor in the environment.  Lookup must succeed.
lookupTyCon :: TyCon -> Environment -> TypeBinding
lookupTyCon tc env =
  case Map.lookup tc $ envTypes env
  of Just b -> b
     Nothing -> internalError $ "lookupTyCon: Not found: " ++ showTyCon tc

lookupVar :: Variable -> Environment -> ValueBinding
lookupVar v env =
  case Map.lookup v $ envValues env
  of Just b -> b
     Nothing -> internalError $ "lookupVar: Not found: " ++ showVariable v

class Monad m => EnvMonad m where
  getEnvironment :: m Environment
  getsEnvironment :: (Environment -> a) -> m a
  getsEnvironment f = liftM f getEnvironment
  withEnvironment :: (Environment -> Environment) -> m a -> m a

getTyConDataType :: EnvMonad m => TyCon -> m (Maybe DataType)
getTyConDataType tc = getsEnvironment lu
  where
    lu env =
      case lookupTyCon tc env
      of TyConAss dt -> Just dt
         _           -> Nothing

getTyConClass :: EnvMonad m => TyCon -> m (Maybe Class)
getTyConClass tc = getsEnvironment lu
  where
    lu env =
      case lookupTyCon tc env
      of TyClsAss c -> Just c
         _          -> Nothing

getTyConTypeFunction :: EnvMonad m => TyCon -> m (Maybe TyFamily)
getTyConTypeFunction tc = getsEnvironment lu
  where
    lu env =
      case lookupTyCon tc env
      of TyFunAss fam -> Just fam
         _            -> Nothing

getVarDataCon :: EnvMonad m => Variable -> m (Maybe DataCon)
getVarDataCon v = getsEnvironment lu
  where
    lu env =
      case lookupVar v env
      of DataConAss dc -> Just dc
         _             -> Nothing

-- | Get the monomorphic type of a recursive variable whose type is being
--   inferred
getRecVarType :: EnvMonad m => Variable -> m HMType
getRecVarType v = getsEnvironment lu
  where
    lu env =
      case lookupVar v env
      of RecVarAss i -> VarTy (recVarType i)
         _           -> internalError "getRecVarType"

getVarBinding :: EnvMonad m => Variable -> m ValueBinding
getVarBinding v = getsEnvironment (lookupVar v)

-- | Add a type parameter to the type environment
withTyParam :: EnvMonad m => TyCon -> m a -> m a
withTyParam tc m = withEnvironment (insertTypeBinding tc TyVarAss) m

withTyParams :: EnvMonad m => [TyCon] -> m a -> m a
withTyParams tcs m = foldr withTyParam m tcs

-------------------------------------------------------------------------------
-- A monad with environment lookup
--
-- Used for generating System F code
newtype TE a = TE {unTE :: ReaderT Environment IO a}

instance Functor TE where
  fmap f (TE m) = TE (fmap f m)

instance Applicative TE where
  pure x = TE (pure x)
  TE f <*> TE x = TE (f <*> x)

instance Monad TE where
  return x = TE (return x)
  TE m >> TE k = TE (m >> k)
  TE m >>= k = TE (m >>= unTE . k)

instance MonadIO TE where liftIO m = TE (liftIO m)

instance UMonad HMType TE where
  freshUVarID = liftIO freshTyVarID

instance EnvMonad TE where
  getEnvironment = TE ask
  getsEnvironment f = TE (asks f)
  withEnvironment f (TE m) = TE (local f m)

instance Supplies TE (Ident SF.Var) where
  fresh = TE $ ReaderT $ \env -> supplyValue $ envSFVarIDSupply env

runTE :: Environment -> TE a -> IO a
runTE env (TE m) = runReaderT m env

{-
-------------------------------------------------------------------------------
-- Type descriptions

-- | Get the System F type corresponding to a type constructor.
--
--   If no type has been assigned, create a new System F type variable and
--   assign it.
tyConToSystemF :: TyCon -> SF.FreshVarM SF.Var
tyConToSystemF tycon =
  case tcDescr tycon
  of TyVarDescr ref -> do
       mx <- liftIO $ readIORef ref
       case mx of
         Just v  -> return v
         Nothing -> assign_new_variable ref
     TyConDescr _ v -> return v
     TyClsDescr cls -> return $ clsTyCon cls
     TyFunDescr fam -> return $ tfTyCon fam
     where
       -- Create a new System F variable and assign it to this one
       assign_new_variable ref = do
         v <- SF.newVar (tcName tycon) SF.TypeLevel
         liftIO $ writeIORef ref $ Just v
         return v


-- | Get the System F information corresponding to a 'TyCon'.
--   The return value is the constructor and a flag indicating whether the
--   constructed type is naturally boxed.
tyConCon :: TyCon -> Maybe (SF.Var, Bool)
tyConCon v =
  case tcDescr v
  of TyConDescr is_boxed v -> Just (v, is_boxed)
     _ -> Nothing

tyConClass :: TyCon -> Maybe Class
tyConClass v =
  case tcDescr v
  of TyClsDescr c -> Just c
     _ -> Nothing

tyConTypeFunction :: TyCon -> Maybe TyFamily
tyConTypeFunction v =
  case tcDescr v
  of TyFunDescr fam -> Just fam
     _ -> Nothing

data TyConDescr =
    -- | A non-unifiable type variable
    TyVarDescr (IORef (Maybe SF.Var))
    -- | A type constructor.  The type constructor includes a flag indicating
    --   whether it is boxed.
  | TyConDescr !Bool SF.Var

    -- | A type class
  | TyClsDescr Class
    
    -- | A type family
  | TyFunDescr TyFamily
-}

-------------------------------------------------------------------------------


-- | A type inference computation takes an environment and returns
--   a generated constraint, a set of placeholders to be solved, and
--   a set of newly created unifiable type variables.
newtype TI a =
  TI {unTI :: RWST Environment (Constraint, Placeholders, [TyVar]) () IO a}

instance Functor TI where
  fmap f (TI m) = TI (fmap f m)

instance Applicative TI where
  pure x = TI (pure x)
  TI f <*> TI x = TI (f <*> x)

instance Monad TI where
  return x = TI (return x)
  TI m >> TI k = TI (m >> k)
  TI m >>= k = TI (m >>= unTI . k)

instance MonadIO TI where liftIO m = TI (liftIO m)

instance UMonad HMType TI where freshUVarID = liftIO freshTyVarID

instance EnvMonad TI where
  getEnvironment = TI ask
  getsEnvironment f = TI (asks f)
  withEnvironment f (TI m) = TI (local f m)

instance Supplies TI (Ident SF.Var) where
  fresh = do env <- getEnvironment
             liftIO $ supplyValue $ envSFVarIDSupply env

-- getSFVarIDSupply :: TI (IdentSupply SF.Var)
-- getSFVarIDSupply = TI $ asks envSFVarIDSupply

runTI :: Environment -> TI a -> IO a
runTI environment (TI m) = do
  (x, (), (constraint, placeholders, tyvars)) <- runRWST m environment ()

  when (not $ null constraint) $
    internalError "runTI: Unresolved constraints after type inference"
  when (not $ null placeholders) $
    internalError "runTI: Unresolved placeholders after type inference"
  when (not $ null tyvars) $
    internalError "runTI: Free type variables remain after type inference"

  return x

liftTE_TI :: TE a -> TI a
liftTE_TI (TE m) = TI $ RWST $ \env s -> do
  x <- runReaderT m env
  return (x, s, mempty)

-- | Create a new, anonymous variable
newAnonymousVariable :: TI Variable
newAnonymousVariable = do
  sf_v <- SF.newAnonymousVar SF.ObjectLevel
  liftIO $ newVariable Nothing (Just sf_v)

-- | Instantiate a type variable and keep track of the variable that was 
--   created.
instantiateTyVar :: TyCon -> TI TyVar
instantiateTyVar v 
  | isTyVar v = do
      v' <- newUVar (tyConName v) (tyConKind v)
      tellNewTyVar v'           -- Keep track of the new variable
      return v'
  | otherwise = internalError "instantiateTyVar: Not a type variable"

-- | Record the fact that a new unifiable type variable was created.
--
--   Variables that remain free after type inference completes will be
--   unified with an 'AnyT' type.
tellNewTyVar :: TyVar -> TI ()
tellNewTyVar v = TI $ tell (mempty, mempty, [v])

-- | Extract the set of free variables produced by the argument. 
--   The set of free variables is cleared.
getFreeVariables :: TI a -> TI (a, [TyVar])
getFreeVariables (TI m) = TI $ RWST $ \r s -> do
  (x, s, (constraint, placeholders, vs)) <- runRWST m r s
  return ((x, vs), s, (constraint, placeholders, []))

-- | Extract the constraint produced by the argument.
--   The constraint is cleared.
getConstraint :: TI a -> TI (a, Constraint)
getConstraint (TI m) = TI $ RWST $ \r s -> do
  (x, s, (constraint, placeholders, vs)) <- runRWST m r s
  return ((x, constraint), s, ([], placeholders, vs))

-- | Extract the placeholders produced by the argument.
--   The placeholders are cleared.
getPlaceholders :: TI a -> TI (a, Placeholders)
getPlaceholders (TI m) = TI $ RWST $ \r s -> do
  (x, s, (constraint, placeholders, vs)) <- runRWST m r s
  return ((x, placeholders), s, (constraint, [], vs))

-- | Raise an exception if the computation creates placeholders
placeholderFree :: TI a -> TI a
placeholderFree m = do
  (x, p) <- getPlaceholders m
  if null p
    then return x
    else internalError "New placeholders may not be created here"

-- | Defer the resolution of a placeholder.  The placeholder is propagated
--   to the next 'getPlaceholders' call.
deferPlaceholder :: Placeholder -> TI ()
deferPlaceholder ph = TI $ tell (mempty, [ph], mempty)

-- | Defer the resolution of some placeholders.  They are propagated
--   to the next 'getPlaceholders' call.
deferPlaceholders :: Placeholders -> TI ()
deferPlaceholders phs = TI $ tell (mempty, phs, mempty)

-- | Require a constraint to hold in the current environment
require :: Constraint -> TI ()
require cst = TI $ tell (cst, mempty, mempty)

-- | Create a dictionary placeholder.  The placeholder's resolution is
--   deferred.
--   In most cases, 'requirePredicate' should be called instead, as it
--   generates a constraint along with the placeholder.
mkDictPlaceholder :: Predicate -> TI Placeholder
mkDictPlaceholder prd = do
  ref <- liftIO $ newIORef Nothing
  let ph = DictPlaceholder $ DictP prd ref
  deferPlaceholder ph
  return ph

-- | Create dictionary placeholders from all predicates in a constraint.
--   Their resolution is deferred.
--   In most cases, 'requireConstraint' should be called instead, as it
--   generates a constraint along with the placeholders.
mkDictPlaceholders :: Constraint -> TI Placeholders
mkDictPlaceholders prds = do
  phs <- liftIO $ forM prds $ \prd -> do 
    ref <- newIORef Nothing
    return $ DictPlaceholder $ DictP prd ref
  deferPlaceholders phs
  return phs

-- | Add a collection of recursive variables of unknown types
--   to the environment.  
assumeRecursiveVariables :: [Variable] -> ([RecVarP] -> TI a) -> TI a
assumeRecursiveVariables vs f = do
  -- Create placeholders and types
  v_infos <- mapM make_info vs
  let insert_vars env = foldr insert_var env $ zip vs v_infos
      insert_var (v, i) env = insertValueBinding v (RecVarAss i) env

  withEnvironment insert_vars $ f (map recVarValue v_infos)
  where
    make_info v = do
      ty <- newUVar Nothing Star
      ref <- liftIO $ newIORef Nothing
      return $ RecVarInfo ty (RecVarP v ref)

-- | Add a monotype to the type environment
assumeMonotype :: EnvMonad m => Variable -> HMType -> m a -> m a
assumeMonotype v t m = withEnvironment (insertValueBinding v (MonoVarAss t)) m

assumeMonotypes :: EnvMonad m => [(Variable, HMType)] -> m a -> m a
assumeMonotypes ((v,t) : bs) m = assumeMonotype v t $ assumeMonotypes bs m
assumeMonotypes []           m = m

assumePolytype :: EnvMonad m => Variable -> TyScheme -> m a -> m a
assumePolytype v t m = withEnvironment (insertValueBinding v (PolyVarAss t)) m

assumePolytypes :: EnvMonad m => [(Variable, TyScheme)] -> m a -> m a
assumePolytypes ((v,t) : bs) m = assumePolytype v t $ assumePolytypes bs m
assumePolytypes []           m = m