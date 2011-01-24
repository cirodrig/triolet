
{-# LANGUAGE TemplateHaskell #-}

module Common.Identifier
    (Ident, Idents, IdentSupply,
     toIdent, fromIdent,
     newIdentSupply, newIdentSupplyAfter
    )
where

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH

import Common.Supply

-- | An identifier is an integer that is used as a unique \"name\" for an
-- object of type @a@.
newtype Ident a = Ident Int
    deriving (Eq, Ord)

type Idents a = [Ident a]
type IdentSupply a = Supply (Ident a)

instance Show (Ident a) where
    show (Ident n) = '#':show n

instance TH.Lift (Ident a) where
    lift (Ident n) = [| Ident n |] 

toIdent :: Int -> Ident a
toIdent = Ident

fromIdent :: Ident a -> Int
fromIdent (Ident n) = n

nextIdent :: Ident a -> Ident a
nextIdent (Ident n) = Ident (n+1)

-- | Start enumerating identifiers from 0
newIdentSupply :: IO (Supply (Ident a))
newIdentSupply = newSupply (Ident 0) nextIdent

-- | Start enumerating identifiers after the given identifier
newIdentSupplyAfter :: Ident a -> IO (Supply (Ident a))
newIdentSupplyAfter x = newSupply (nextIdent x) nextIdent

