
module Pyon.Untyped.HMType
where

import qualified Data.Set as Set

data TyCon
type TyVarSet = Set.Set TyCon

data HMType

instance Eq TyCon
instance Ord TyCon

