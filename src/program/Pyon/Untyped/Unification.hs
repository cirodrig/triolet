
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
import Pyon.Untyped.Data

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

-------------------------------------------------------------------------------
-- Pretty-printing

-- | Run a pretty-printer.  Within the scope of this pretty-printer, anonymous
-- variables will be assigned a temporary name.  The name may be different
-- between different calls to 'runPpr'.
runPpr :: Ppr a -> IO a
runPpr m = do
  -- Names for anonymous type variables
  names <- newIORef $ concatMap sequence $ drop 1 $ inits $ repeat ['a' .. 'z']

  -- Empty environment
  tenv <- newIORef Map.empty
  penv <- newIORef Map.empty
  
  doPpr m (PprContext names tenv penv)

-- | Get a new variable name.
pprGetFreshName :: Ppr String
pprGetFreshName = Ppr $ \env -> do
  (nm:nms) <- readIORef $ freshNames env
  writeIORef (freshNames env) nms
  return nm

-- | Get the name of a type variable; assign a new name if needed.
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

-- | Get the name of a parameter passing convention variable; assign a
-- new name if needed.
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

