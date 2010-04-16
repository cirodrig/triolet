
module Pyon.Untyped.Unification
       (Substitution, substTc, substCc,
        emptySubstitution, substitutionFromList, substitution,
        updateTc, updateCc,
        Ppr, runPpr, pprGetTyConName, pprGetPassConvVarName,
        Predicate(..),
        Constraint,
        Unifiable(..),
        Type(..)
       )
where

import Control.Applicative
import Control.Monad.Trans
import Data.IORef
import Data.List
import qualified Data.Map as Map
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Identifier
import Gluon.Common.SourcePos
import {-# SOURCE #-} Pyon.Untyped.HMType
import {-# SOURCE #-} Pyon.Untyped.CallConv
import {-# SOURCE #-} Pyon.Untyped.GenSystemF

-- | A substitution for type constructors
data Substitution =
  Substitution
  { _substTc :: Map.Map TyCon HMType
  , _substCc :: Map.Map PassConvVar PassConv
  }

substTc = _substTc
substCc = _substCc

emptySubstitution :: Substitution
emptySubstitution = Substitution Map.empty Map.empty

substitutionFromList :: [(TyCon, HMType)] -> Substitution
substitutionFromList xs = Substitution (Map.fromList xs) Map.empty

substitution :: Map.Map TyCon HMType 
             -> Map.Map PassConvVar PassConv 
             -> Substitution
substitution = Substitution

updateTc :: (Map.Map TyCon HMType -> Map.Map TyCon HMType) 
         -> Substitution -> Substitution
updateTc f s = s {_substTc = f $ substTc s}

updateCc :: (Map.Map PassConvVar PassConv -> Map.Map PassConvVar PassConv)
         -> Substitution -> Substitution
updateCc f s = s {_substCc = f $ substCc s}

-- | A pretty-printing applicative construct for giving names to
-- anonymous variables
newtype Ppr a = Ppr {doPpr :: PprContext -> IO a}

data PprContext =
  PprContext
  { freshNames :: {-# UNPACK #-} !(IORef [String])
  , typeNames :: {-# UNPACK #-} !(IORef (Map.Map (Ident TyCon) Doc))
  , passNames :: {-# UNPACK #-} !(IORef (Map.Map (Ident PassConvVar) Doc))
  }

runPpr :: Ppr a -> IO a
runPpr m = do
  -- Names for anonymous type variables
  names <- newIORef $ concatMap sequence $ drop 1 $ inits $ repeat ['a' .. 'z']

  -- Empty environment
  tenv <- newIORef Map.empty
  penv <- newIORef Map.empty
  
  doPpr m (PprContext names tenv penv)

pprGetFreshName :: Ppr String
pprGetFreshName = Ppr $ \env -> do
  (nm:nms) <- readIORef $ freshNames env
  writeIORef (freshNames env) nms
  return nm

pprGetTyConName :: Ident TyCon -> Ppr Doc
pprGetTyConName ident = Ppr $ \env -> do
  nenv <- readIORef $ typeNames env
  case Map.lookup ident nenv of
    Just doc -> return doc
    Nothing -> do
      nm <- doPpr pprGetFreshName env
      let doc = text nm
      
      -- Save name in environment
      writeIORef (typeNames env) $ Map.insert ident doc nenv
      
      return doc

pprGetPassConvVarName :: Ident PassConvVar -> Ppr Doc
pprGetPassConvVarName ident = Ppr $ \env -> do
  nenv <- readIORef $ passNames env
  case Map.lookup ident nenv of
    Just doc -> return doc
    Nothing -> do
      nm <- doPpr pprGetFreshName env
      let doc = text nm
      
      -- Save name in environment
      writeIORef (passNames env) $ Map.insert ident doc nenv
      
      return doc

instance Functor Ppr where
  fmap f (Ppr g) = Ppr $ \env -> fmap f (g env)

instance Applicative Ppr where
  pure x = Ppr $ \_ -> return x
  Ppr ff <*> Ppr xx = Ppr $ \env -> do f <- ff env
                                       x <- xx env
                                       return $ f x

instance Monad Ppr where
  return = pure
  Ppr ff >>= kk = Ppr $ \env -> do x <- ff env
                                   doPpr (kk x) env

instance MonadIO Ppr where
  liftIO m = Ppr $ \_ -> m

-- | A predicate to be solved by type inference
data Predicate =
    -- | Class membership.  This predicate translates to a class dictionary.
    IsInst HMType !Class
    -- | Parameter-passing constraint.  This predicate translates to
    -- parameter-passing information, such as how to load, store, or
    -- duplicate a value.
  | HasPassConv HMType PassConv
    -- | Equality constraint on parameter-passing conventions
  | EqPassConv PassConv PassConv
    -- | Equality constraint on execution modes
  | EqExecMode ExecMode ExecMode

type Constraint = [Predicate]

class Unifiable a where
  -- | Show some unifiable objects.  Temporary names may be assigned to 
  -- anonymous variables; the same names are used across all objects.  
  -- This is used when constructing messages for unification failure.
  uShow :: a -> Ppr Doc

  -- | Rename a unifiable object
  rename :: Substitution -> a -> IO a
  
  -- | Unify terms.  Unification may produce extra constraints, which should
  -- be added to any constraints already in the context.  Flexible type 
  -- variables may be modified during unification.  If the arguments cannot 
  -- be unified, an exception is thrown.
  unify :: SourcePos -> a -> a -> IO Constraint
  
  -- | Match (semi-unify) two terms. 
  --
  -- @match x y@ finds a substitution that unifies @x@ with @y@, if one exists.
  -- If no substitution can be found, return None.  The terms are not modified.
  match :: a -> a -> IO (Maybe Substitution)

  -- | Decide whether two unifiable terms are equal.
  -- The terms are not modified.
  uEqual :: a -> a -> IO Bool

class Type a where
  -- | Get the set of free type variables mentioned in the value
  freeTypeVariables :: a -> IO TyVarSet

