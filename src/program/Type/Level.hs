-- | Level definitions in the type hierarchy.

{-# LANGUAGE TemplateHaskell #-}
module Type.Level where

import Data.Typeable
import Language.Haskell.TH.Syntax(Lift(..))

data Level = ObjectLevel | TypeLevel | KindLevel | SortLevel
             deriving(Eq, Ord, Enum, Show, Bounded, Typeable)

-- Convert a level to a human-readable work
levelWord :: Level -> String
levelWord ObjectLevel = "object"
levelWord TypeLevel = "type"
levelWord KindLevel = "kind"
levelWord SortLevel = "sort"

class HasLevel a where
    getLevel :: a -> Level

instance Lift Level where
    lift ObjectLevel = [| ObjectLevel |]
    lift TypeLevel   = [| TypeLevel |]
    lift KindLevel   = [| KindLevel |]
    lift SortLevel   = [| SortLevel |]
