{-| External representation of variable names.  Variable names have to be
-- mangled to avoid cross-file name clashes.
-}

{-# LANGUAGE TemplateHaskell #-}
module Common.Label
       (ModuleName(..),
        builtinModuleName,
        LabelTag(..),
        LocalID(..),
        newLocalIDSupply,
        showLocalID,
        Label(..),
        showLabel,
        labelLocalNameAsString,
        builtinLabel,
        plainLabel,
        externLabel,
        anonymousLabel,
        cloneLabel,
        mangleLabel,
        mangleModuleScopeLabel
       )
where

import Control.DeepSeq
import Language.Haskell.TH.Syntax(Lift(..))

import Common.Error
import Common.Identifier
import Common.Supply
import LowLevel.Types

newtype ModuleName = ModuleName {showModuleName :: String}
                   deriving(Eq, Ord, Show)

instance NFData ModuleName where rnf (ModuleName s) = rnf s

instance Lift ModuleName where
  lift (ModuleName s) = [| ModuleName s |]

builtinModuleName :: ModuleName
builtinModuleName = ModuleName "Builtin"

-- | A label tag, used to distinguish multiple variables that were created
--   from the same original variable.
--
--   Label tags are purely cosmetic extensions of variable names.  They
--   help to produce readable names in the generated code.  They have no
--   semantic significance.
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

instance NFData LabelTag where rnf t = t `seq` () 

-- | A local variable ID.  Local variable IDs are assigned to anonymous
--   variables that will be exported from a module.
newtype LocalID = LocalID Int deriving(Eq, Ord)

instance NFData LocalID where rnf (LocalID n) = rnf n

newLocalIDSupply :: IO (Supply LocalID)
newLocalIDSupply = newSupply (LocalID 0) (\(LocalID n) -> LocalID (1+n))

showLocalID :: LocalID -> String
showLocalID (LocalID n) = show n

-- | A label of low-level code.  Labels encode everything about a variable
--   name (except for the variable ID).
--   A variable must have a unqiue label if it's visible outside its own 
--   module.  In general, variables that are local to a module don't have 
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

instance NFData Label where
  rnf (Label m n t e) = rnf m `seq` rnf n `seq` rnf t `seq` rnf e

-- | Print a human-readable summary of the label.
showLabel :: Label -> String
showLabel lab =
  let base = case labelLocalName lab
             of Left str -> str
                Right id -> showLocalID id
      tag = encodeLabelTag (labelTag lab)
      tagstr = if null tag then "" else '\'' : tag
  in base ++ tagstr

labelLocalNameAsString :: Label -> String
labelLocalNameAsString l =
  case labelLocalName l
  of Left s  -> s
     Right _ -> internalError "labelLocalNameAsString: Name is not a string"

-- | A label of a builtin Pyon variable
builtinLabel :: String -> Label
builtinLabel name = plainLabel builtinModuleName name

-- | A label of a regular Pyon variable
plainLabel :: ModuleName -> String -> Label
plainLabel mod name = Label mod (Left name) NormalLabel Nothing

-- | A label of a Pyon variable with an external name
externLabel :: ModuleName -> String -> Maybe String -> Label
externLabel mod name ext_name =
  Label mod (Left name) NormalLabel ext_name

-- | A label of a Pyon variable with a local ID instead of a string name
anonymousLabel :: ModuleName -> LocalID -> Maybe String -> Label
anonymousLabel mod id ext_name =
  Label mod (Right id) NormalLabel ext_name

-- | Create a label that is like the given label and can be attached to a
--   different variable.  Anything that would cause a name conflict, such
--   as an external name, is removed.  The cloned label must not be externally
--   visible.
cloneLabel :: Label -> Label
cloneLabel lab = lab {labelExternalName = Nothing}

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
