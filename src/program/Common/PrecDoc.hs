{-| Utilities for generating docstrings with parentheses when necessary.
-}

module Common.PrecDoc
       (Prec(..),
        outerPrec, stmtPrec, typeAnnPrec, lamPrec, funPrec, appPrec, atomicPrec,
        PrecDoc,
        hasPrec, hasAtomicPrec,
        precedence,
        unparenthesized,
        (?), (?+)
       )
where

import Text.PrettyPrint.HughesPJ

infix 2 `hasPrec`
infix 8 ?, ?+

-- | An expression precedence.  Higher precedences bind more tightly.
newtype Prec = Prec Int deriving (Eq, Ord, Show)

-- | A precedence lower than the lowest valid precedence.  Formatting a
--   docstring in a place with this precedence ensures that it never gets
--   parenthesized.
outerPrec :: Prec
outerPrec = Prec (-1)

-- | The precedence of a statement-like expression, such as \"let\" or \"case\"
stmtPrec :: Prec
stmtPrec = Prec 0

-- | The precedence of a type annotation
typeAnnPrec :: Prec
typeAnnPrec = Prec 4

-- | The precedence of a type function
lamPrec :: Prec
lamPrec = Prec 5

-- | The precedence of a function type
funPrec :: Prec
funPrec = Prec 6

-- | The precedence of function application
appPrec :: Prec
appPrec = Prec 16

-- | The precedence of an expression that should never be parenthesized.
atomicPrec :: Prec
atomicPrec = Prec 20

-- | A docstring with operator precedence.  The precedence is used to decide
--   whether to parenthesize the docstring when it is displayed.
--   The precedence given is the precedence of the docstring's outermost term.
data PrecDoc = PrecDoc {-#UNPACK#-}!Prec Doc

instance Show PrecDoc where
  show (PrecDoc _ d) = show d

-- | Assign a precedence to a 'Doc'
hasPrec :: Doc -> Prec -> PrecDoc
d `hasPrec` p = PrecDoc p d

hasAtomicPrec :: Doc -> PrecDoc
hasAtomicPrec d = d `hasPrec` atomicPrec

-- | Get the precedence of a 'PrecDoc'
precedence :: PrecDoc -> Prec
precedence (PrecDoc p _) = p

-- | Format the document without parentheses
unparenthesized :: PrecDoc -> Doc
unparenthesized d = d ? outerPrec

-- | The document @pdoc ? pr@ is formatted without parentheses if @pdoc@ has
--   at least precedence @pr@, or with parentheses othewise.
(?) :: PrecDoc -> Prec -> Doc
PrecDoc (Prec n) doc ? (Prec context)
  | n >= context = doc
  | otherwise    = parens doc
                  
-- | The document @pdoc ?+ pr@ is formatted without parentheses if @pdoc@ has
--   precedence greater than @pr@, or with parentheses othewise.
(?+) :: PrecDoc -> Prec -> Doc
PrecDoc (Prec n) doc ?+ (Prec context)
  | n > context = doc
  | otherwise   = parens doc
