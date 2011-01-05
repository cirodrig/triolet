{-| External representation of variable names.  Variable names have to be
-- mangled to avoid cross-file name clashes.
-}
module LowLevel.Label
       (ModuleName,
        moduleName,
        builtinModuleName,
        showModuleName,
        LabelTag(..),
        LocalID(..),
        newLocalIDSupply,
        showLocalID,
        Label(..),
        labelLocalNameAsString,
        pyonLabel,
        externPyonLabel,
        anonymousPyonLabel,
        mangleLabel,
        mangleModuleScopeLabel
       )
where

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Supply
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
    -- | A global function vector entry point.
  | VectorEntryLabel
    -- | A global function exact entry point.
  | ExactEntryLabel
    -- | A global function inexact entry point.
  | InexactEntryLabel
    deriving(Eq, Ord, Enum, Bounded)

-- | A local variable ID.  Local variable IDs are assigned to anonymous
--   variables that will be exported from a module.
newtype LocalID = LocalID Int deriving(Eq, Ord)

newLocalIDSupply :: IO (Supply LocalID)
newLocalIDSupply = newSupply (LocalID 0) (\(LocalID n) -> LocalID (1+n))

showLocalID :: LocalID -> String
showLocalID (LocalID n) = show n

-- | A label of low-level code.  Labels encode everything about a variable
--   name (except for the variable ID).
--   A variable must have a unqiue label if it's visible outside its own 
--   module.  In general, varaibles that are local to a module don't have 
--   labels.
data Label =
  Label 
  { -- | The module where a variable was defined
    labelModule       :: !ModuleName

    -- | The variable name.
  , labelLocalName    :: !(Either String LocalID)

    -- | Tags to disambiguate multiple variables with the same name
  , labelTag          :: !LabelTag
    
    -- | If present, this is the variable's name, overriding the normal 
    --   name mangling process.  External names can be referenced from
    --   non-Pyon code.  Only externally visible variables may have an
    --   external name.
  , labelExternalName :: !(Maybe String)
  }
  deriving(Eq, Ord)

labelLocalNameAsString :: Label -> String
labelLocalNameAsString l =
  case labelLocalName l
  of Left s  -> s
     Right _ -> internalError "labelLocalNameAsString: Name is not a string"

-- | A label of a regular Pyon variable
pyonLabel :: ModuleName -> String -> Label
pyonLabel mod name = Label mod (Left name) NormalLabel Nothing

-- | A label of a Pyon variable with an external name
externPyonLabel :: ModuleName -> String -> Maybe String -> Label
externPyonLabel mod name ext_name =
  Label mod (Left name) NormalLabel ext_name

-- | A label of a Pyon variable with a local ID instead of a string name
anonymousPyonLabel :: ModuleName -> LocalID -> Maybe String -> Label
anonymousPyonLabel mod id ext_name =
  Label mod (Right id) NormalLabel ext_name

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
encodeLabelTag VectorEntryLabel  = "qV"
encodeLabelTag ExactEntryLabel   = "qE"
encodeLabelTag InexactEntryLabel = "qF"

-- | Mangle a label.
mangleLabel :: Label -> String
mangleLabel name
  | Just xname <- labelExternalName name = xname
  | otherwise =
      "_pi_" ++
      encodeNameString (showModuleName $ labelModule name) ++ "_" ++
      either encodeNameString showLocalID (labelLocalName name) ++
      encodeLabelTag (labelTag name)

-- | Mangle a label without the module name.  The label should only be used
-- at module scope, since it may conflict with different names in other
-- modules.
mangleModuleScopeLabel :: Label -> String
mangleModuleScopeLabel name =
  "_pi__" ++
  either encodeNameString showLocalID (labelLocalName name) ++
  encodeLabelTag (labelTag name)
