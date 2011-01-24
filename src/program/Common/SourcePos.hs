-- | An abstraction of source code information.  This is used throughout the
-- compiler to keep track of where a bit of IR came from.

{-# LANGUAGE TemplateHaskell #-}
module Common.SourcePos
    (SourcePos,
     fileSourcePos, moduleSourcePos, noSourcePos,
     sourceFile, sourceLine, sourceColumn,
     setSourceLine, setSourceColumn,
     HasSourcePos(..)
    )
where

import Data.Typeable
import Language.Haskell.TH.Syntax(Lift(..))

import Common.Label

data SourcePos =
    Pos
    { _sourceFile :: !FilePath
    , _sourceLine :: {-# UNPACK #-} !Int
    , _sourceColumn :: {-# UNPACK #-} !Int
    }
  | Module
    { _sourceModule :: ModuleName
    }
  | Unknown
    deriving(Eq, Typeable)

isPos (Pos _ _ _) = True
isPos _           = False

instance Show SourcePos where
    show (Pos f l c) = f ++ ": " ++ show l ++ ", " ++ show c
    show (Module m)  = "Module '"  ++ showModuleName m ++ "'"
    show Unknown     = "<no source information>"

instance Lift SourcePos where
    lift (Pos f l c) = [| Pos f l c |]
    lift (Module m)  = [| Module m |]
    lift Unknown     = [| Unknown |]

fileSourcePos :: FilePath -> Int -> Int -> SourcePos
fileSourcePos f l c = Pos f l c

moduleSourcePos :: ModuleName -> SourcePos
moduleSourcePos n = Module n

noSourcePos :: SourcePos
noSourcePos = Unknown

sourceFile (Pos f _ _) = Just f
sourceFile Unknown     = Nothing

sourceLine (Pos _ l _) = Just l
sourceLine Unknown     = Nothing

sourceColumn (Pos _ _ c) = Just c
sourceColumn Unknown    = Nothing

setSourceLine l p | isPos p   = p {_sourceLine = l}
                  | otherwise = p

setSourceColumn c p | isPos p   = p {_sourceColumn = c}
                    | otherwise = p

class HasSourcePos a where
    getSourcePos :: a -> SourcePos

