
{-# LANGUAGE Rank2Types, FlexibleInstances #-}
module LowLevel.FreshVar
       (FreshVarM, runFreshVarM)
where

import Control.Monad.ST

import Gluon.Common.Supply
import Gluon.Common.Identifier

import {-# SOURCE #-} LowLevel.Syntax

-- | A monad supplying fresh variables
newtype FreshVarM a = FreshVarM (forall st. IdentSupply Var -> ST st a)

runFreshVarM id_supply (FreshVarM f) = stToIO (f id_supply)

instance Functor FreshVarM where
  fmap f (FreshVarM g) = FreshVarM (\supply -> fmap f (g supply))

instance Monad FreshVarM where
  return x = FreshVarM (\_ -> return x)
  FreshVarM f >>= k = FreshVarM (\supply -> do
                                    x <- f supply
                                    case k x of FreshVarM g -> g supply)

instance Supplies FreshVarM (Ident Var) where
  fresh = FreshVarM (\x -> unsafeIOToST (supplyValue x))
  supplyToST f = FreshVarM (\x -> let get_fresh = unsafeIOToST (supplyValue x)
                                  in f get_fresh)

