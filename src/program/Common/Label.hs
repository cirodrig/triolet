{-| External representation of variable names.  Variable names have to be
-- mangled to avoid cross-file name clashes.
-}

{-# LANGUAGE TemplateHaskell #-}
module Common.Label
       (ModuleName(..),
        builtinModuleName,
        LabelTag(..),
        isEntryPointTag,
        LocalID(..),
        newLocalIDSupply,
        showLocalID,
        Label(..),
        appendLabelTag,
        showLabel,
        labelLocalNameAsString,
        builtinLabel,
        plainLabel,
        externLabel,
        anonymousLabel,
        cloneLabel,
        mangleLabel,
        mangleModuleScopeLabel,
        
        -- * Label maps
        HasLabel(..), getLabel',
        LabelMap,
        labelMap,
        labelMapRestriction,
        labelMapUnion,
        labelMapContains,
        labelMapDoesn'tContain
       )
where

import Control.DeepSeq
import qualified Data.Map as Map
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
--   Label tags are used as a stable way of identifying such variables.
--   Because label tags are created in a reliable way, a variable always
--   gets the same label under separate compilation, though it may get
--   multiple IDs.  Thanks to label tags, when the compiler reads multiple
--   files, it can rename variables so that their IDs are consistent.
data LabelTag =
    -- | A global function info table.
    InfoTableLabel
    -- | A global function direct entry point.
  | DirectEntryLabel
    -- | A global function vector entry point.
  | VectorEntryLabel
    -- | A global function exact entry point.
  | ExactEntryLabel
    -- | A global function inexact entry point.
  | InexactEntryLabel
    -- | A serializer function of a data type or data constructor
  | SerializerLabel
    -- | A deserializer function of a data type or data constructor
  | DeserializerLabel
    deriving(Eq, Ord, Enum, Bounded)

-- | Whether the tag denotes one of the entry points created by closure
--   conversion.
isEntryPointTag :: LabelTag -> Bool
isEntryPointTag InfoTableLabel    = True
isEntryPointTag DirectEntryLabel  = True
isEntryPointTag VectorEntryLabel  = True
isEntryPointTag ExactEntryLabel   = True
isEntryPointTag InexactEntryLabel = True
isEntryPointTag SerializerLabel   = False
isEntryPointTag DeserializerLabel = False

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

    -- | Tags to disambiguate multiple variables with the same name.
    --   Order of tags is significant.
    --   A new label may be derived from an old one by appending a tag
    --   to the list.
  , labelTags         :: ![LabelTag]
    
    -- | If present, this is the variable's name, overriding the normal 
    --   name mangling process.  External names can be referenced from
    --   non-Triolet code.  Only externally visible variables may have an
    --   external name.
    --
    --   If a function has an external name, it must not have tags.
    --   Other tags arise on entities created by the compilation process;
    --   these entities are not visible to non-Triolet code.
  , labelExternalName :: !(Maybe String)
  }
  deriving(Eq, Ord)

instance NFData Label where
  rnf (Label m n t e) = rnf m `seq` rnf n `seq` rnf t `seq` rnf e

appendLabelTag :: LabelTag -> Label -> Label
appendLabelTag tag lab = lab {labelTags = labelTags lab ++ [tag]}

-- | Print a human-readable summary of the label.
showLabel :: Label -> String
showLabel lab =
  let base = case labelLocalName lab
             of Left str -> str
                Right id -> showLocalID id
      tagstr = concat ['\'': labelTagString t | t <- labelTags lab]
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
plainLabel mod name = Label mod (Left name) [] Nothing

-- | A label of a Pyon variable with an external name
externLabel :: ModuleName -> String -> Maybe String -> Label
externLabel mod name ext_name =
  Label mod (Left name) [] ext_name

-- | A label of a Pyon variable with a local ID instead of a string name
anonymousLabel :: ModuleName -> LocalID -> Maybe String -> Label
anonymousLabel mod id ext_name =
  Label mod (Right id) [] ext_name

-- | Create a label that is like the given label and can be attached to a
--   different variable.  Anything that would cause a name conflict, such
--   as an external name, is removed.  The cloned label must not be externally
--   visible.
cloneLabel :: Label -> Label
cloneLabel lab = lab {labelExternalName = Nothing, labelTags = []}

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
encodeLabelTags :: [LabelTag] -> String
encodeLabelTags ts = concat $ map ('q':) $ map labelTagString ts

-- | Encode a label tag as a string.
labelTagString :: LabelTag -> String
labelTagString InfoTableLabel    = "I"
labelTagString DirectEntryLabel  = "D"
labelTagString VectorEntryLabel  = "V"
labelTagString ExactEntryLabel   = "E"
labelTagString InexactEntryLabel = "F"
labelTagString SerializerLabel   = "R"
labelTagString DeserializerLabel = "S"

-- | Mangle a label.
mangleLabel :: Label -> String
mangleLabel name
  | Just xname <- labelExternalName name = xname
  | otherwise =
      "_pi_" ++
      encodeNameString (showModuleName $ labelModule name) ++ "_" ++
      either encodeNameString showLocalID (labelLocalName name) ++
      encodeLabelTags (labelTags name)

-- | Mangle a label without the module name.  The label should only be used
-- at module scope, since it may conflict with different names in other
-- modules.
mangleModuleScopeLabel :: Label -> String
mangleModuleScopeLabel name =
  "_pi__" ++
  either encodeNameString showLocalID (labelLocalName name) ++
  encodeLabelTags (labelTags name)

-------------------------------------------------------------------------------
-- Label maps

-- | Variables with optional labels
class HasLabel var where getLabel :: var -> Maybe Label

getLabel' :: HasLabel var => var -> Label
getLabel' v = case getLabel v
              of Just l  -> l
                 Nothing -> internalError "getLabel': No label"

-- | A map fom labels to labeled variables
type LabelMap var = Map.Map Label var

-- | Create a label map from a list of variables.
--   Order is important: if there are multiple variables with the same
--   label, the last one will be in the map.
labelMap :: HasLabel var => [var] -> LabelMap var
labelMap vs = Map.fromList $ map assoc vs
  where
    assoc v = let !label = getLabel' v in (label, v)

-- | Take the subset of the 'labelMap' whose labels match one of the given
--   variables
labelMapRestriction :: HasLabel var => LabelMap var -> [var] -> LabelMap var
labelMapRestriction m vars =
  Map.intersection m $ labelMap vars

-- | Take the union of two 'LabelMap's.  Common keys must have the same
--   value and the resulting map must be injective on IDs. 
labelMapUnion :: LabelMap var -> LabelMap var -> LabelMap var
labelMapUnion = Map.union

-- | Check whether the given externally visible variable's label
--   is a key in the label map
labelMapContains :: HasLabel var => LabelMap var -> var -> Bool
labelMapContains m v = getLabel' v `Map.member` m

labelMapDoesn'tContain :: HasLabel var => LabelMap var -> var -> Bool
labelMapDoesn'tContain m v = not $ labelMapContains m v
