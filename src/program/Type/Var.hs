
{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances #-}
{-# OPTIONS_GHC -no-auto #-}
module Type.Var
       (Var, varID, varName, 
        VarID,
        pprVar,
        mkVar, mkAnonymousVar, mkClonedVar,
        newVar, newAnonymousVar, newClonedVar, newTaggedVar,
        FreshVarM,
        runFreshVarM)
where

import Control.Applicative
import Control.DeepSeq
import Control.Monad
import Control.Monad.Trans
import Text.PrettyPrint.HughesPJ

import Common.Identifier
import Common.Supply
import Common.Label
import Type.Level

-- | A variable or constructor.
--
-- Each 'Var' has a unique identifier.  If two variables have the same
-- identifier, their other fields are equal.
data Var =
  Var { _varID :: {-# UNPACK #-} !(Ident Var)
      , _varName :: !(Maybe Label)
      , _varLevel :: !Level
      }

instance Eq Var where
  v1 == v2 = _varID v1 == _varID v2
  v1 /= v2 = _varID v1 /= _varID v2

instance Ord Var where
  compare v1 v2 = compare (_varID v1) (_varID v2)

instance Show Var where
  show v =
    let name = case _varName v
               of Nothing -> "_"
                  Just lab -> showLabel lab
    in name ++ "'" ++ show (fromIdent $ _varID v)

instance HasLevel Var where
  getLevel v = _varLevel v

instance NFData Var where
  rnf (Var id n l) = rnf id `seq` rnf n `seq` rnf l

type VarID = Ident Var
  
varID :: Var -> Ident Var
{-# INLINE varID #-}
varID v = _varID v

varName :: Var -> Maybe Label
varName = _varName

mkVar :: VarID -> Maybe Label -> Level -> Var
mkVar = Var

mkAnonymousVar :: VarID -> Level -> Var
mkAnonymousVar id lv = mkVar id Nothing lv

mkClonedVar :: VarID -> Var -> Var
mkClonedVar id old_v =
  let new_lab = fmap cloneLabel $ varName old_v
  in mkVar id new_lab (getLevel old_v)

newVar :: (Monad m, Supplies m VarID) => Maybe Label -> Level -> m Var
newVar lab lv = do
  id <- fresh
  return $ mkVar id lab lv

newAnonymousVar :: (Monad m, Supplies m VarID) => Level -> m Var
newAnonymousVar lv = newVar Nothing lv

newClonedVar :: (Monad m, Supplies m VarID) => Var -> m Var
newClonedVar v = do
  id <- fresh
  return $ mkClonedVar id v

-- | Create a new variable that is like the given variable, but with a tag 
--   added to its label.  Error if the variable has no label.
newTaggedVar :: (Monad m, Supplies m VarID) => LabelTag -> Var -> m Var
newTaggedVar tag v =
  let lab = case varName v
            of Just lab -> appendLabelTag tag lab
  in newVar (Just lab) (getLevel v)

pprVar :: Var -> Doc
pprVar v = text (show v)

-- | A monad for performing simple computations that require a variable
--   supply
newtype FreshVarM a = FreshVarM (IdentSupply Var -> IO a)

runFreshVarM :: IdentSupply Var -> FreshVarM a -> IO a
runFreshVarM supply (FreshVarM f) = f supply

instance Functor FreshVarM where
  fmap f (FreshVarM g) = FreshVarM (\env -> fmap f (g env))

instance Applicative FreshVarM where
  pure = return
  (<*>) = ap

instance Monad FreshVarM where
  return x = FreshVarM (\_ -> return x)
  m >>= k = FreshVarM $ \env ->
    case m
    of FreshVarM f1 -> do x <- f1 env
                          case k x of FreshVarM f2 -> f2 env

instance MonadIO FreshVarM where
  liftIO m = FreshVarM (\_ -> m)

instance Supplies FreshVarM (Ident Var) where
  fresh = FreshVarM supplyValue
