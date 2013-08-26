
module Common.ConPattern where

import Data.List

-- | 'ConPatterns' represent static knowledge of what value is stored
--   in a variable.  They are similar to, but less precise than, 'AbsValue's.
--
--   'ConPatterns' are used for controlling inlining.  Their motivating use
--   case is structurally recursive functions.  Such functions should be
--   inlined only for the parts of the structure that are statically known.
--   A 'ConPattern' specifies what should be known about a parameter in order
--   for inlining to be profitable.
data ConPattern =
    ConTerm ConPatterns    -- ^ An application of a constructor
                           --   to arguments matching the given patterns.
                           --   Only for product types (which have only
                           --   one possible constructor).
  | AnyConTerm             -- ^ Any constructor application
  | AnyTerm                -- ^ Any term
    deriving(Eq)

type ConPatterns = [ConPattern]

showConPatterns :: ConPatterns -> String
showConPatterns ps = "(" ++ intercalate " " (map showConPattern ps) ++ ")"

showConPattern :: ConPattern -> String
showConPattern (ConTerm ps) = "D" ++ showConPatterns ps
showConPattern AnyConTerm = "C"
showConPattern AnyTerm = "T"

