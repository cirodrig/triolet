
{-# LANGUAGE DeriveDataTypeable #-}
module Untyped.Kind where

import Data.Typeable(Typeable)
import Text.PrettyPrint.HughesPJ

infixr :->
data Kind = Star | Kind :-> Kind
          deriving(Eq, Typeable)

showKind :: Kind -> String
showKind Star = "*"
showKind (Star :-> k) = "* -> " ++ showKind k
showKind (k :-> k') = "(" ++ showKind k ++ ") -> " ++ showKind k'

pprKind :: Kind -> Doc
pprKind k = text $ showKind k

-- | The kind of a constructor that takes N parameters of kind @*@
nAryKind :: Int -> Kind
nAryKind n = iterate (Star :->) Star !! n