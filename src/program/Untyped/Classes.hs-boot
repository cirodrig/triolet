
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
module Untyped.Classes
    (reduceTypeFunction) where

import Text.PrettyPrint.HughesPJ
import Untyped.Unif
import Untyped.Type
import Untyped.TIMonad

reduceTypeFunction :: NormalizeContext HMType m
                   => TyFamily  -- ^ Type function to evaluate
                   -> [HMType]  -- ^ Arguments to the type function
                   -> m (Maybe HMType) -- ^ Reduced type (if reducible)

