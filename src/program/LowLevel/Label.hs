{-| External representation of variable names.  Variable names have to be
-- mangled to avoid cross-file name clashes.
-}
module LowLevel.Label
       (ModuleName,
        moduleName,
        builtinModuleName,
        showModuleName,
        LabelTag(..),
        Label(..),
        pyonLabel,
        externPyonLabel,
        mangleLabel
       )
where

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label(ModuleName, builtinModuleName, moduleName, showModuleName)
import LowLevel.Types

-- | A label tag, used to distinguish multiple variables that were created
-- from the same original variable.
data LabelTag =
    -- | A normal variable.  This tag is used on procedures, global data, and
    --   global function closures.
    NormalLabel
    -- | A global function direct entry point.
  | DirectEntryLabel
    -- | A global function exact entry point.
  | ExactEntryLabel
    -- | A global function inexact entry point.
  | InexactEntryLabel
    deriving(Eq, Ord)

-- | A label of low-level code.  Labels encode everything about a variable
--   name (except for the variable ID).  Variables do not in general have
--   unique labels, but externally visible variables have unique labels.
data Label =
  Label 
  { -- | The module where a variable was defined
    labelModule       :: !ModuleName

    -- | The variable name
  , labelLocalName    :: !String

    -- | Tags to disambiguate multiple variables with the same name
  , labelTag          :: !LabelTag
    
    -- | If present, this is the variable's name, overriding the normal 
    --   name mangling process.  External names can be referenced from
    --   non-Pyon code.  Only externally visible variables may have an
    --   external name.
  , labelExternalName :: !(Maybe String)
  }
  deriving(Eq)

-- | A label of a regular Pyon variable
pyonLabel :: ModuleName -> String -> Label
pyonLabel mod name = Label mod name NormalLabel Nothing

-- | A label of a Pyon variable with an external name
externPyonLabel :: ModuleName -> String -> Maybe String -> Label
externPyonLabel mod name ext_name = Label mod name NormalLabel ext_name

-- | Encode a string appearing in a name.  Characters used by mangling are
-- replaced by a two-character string beginning with \'q\'.
encodeNameString :: String -> String
encodeNameString s = concatMap encodeLetter s
  where
    encodeLetter '_' = "qu"
    encodeLetter '.' = "qd"
    encodeLetter 'q' = "qq"
    encodeLetter c   = [c]

-- | Encode a label tag as a string.  Normally this appears as a component of 
-- a mangled label.
encodeLabelTag :: LabelTag -> String
encodeLabelTag NormalLabel       = ""
encodeLabelTag DirectEntryLabel  = "qD"
encodeLabelTag ExactEntryLabel   = "qE"
encodeLabelTag InexactEntryLabel = "qF"

-- | Mangle a label.
mangleLabel :: Label -> String
mangleLabel name
  | Just xname <- labelExternalName name = xname
  | otherwise =
      "_pi_" ++
      encodeNameString (showModuleName $ labelModule name) ++ "_" ++
      encodeNameString (labelLocalName name) ++
      encodeLabelTag (labelTag name)
