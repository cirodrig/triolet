{-| External representation of variable names.  Variable names have to be
-- mangled to avoid cross-file name clashes.
-}
module LowLevel.Label where

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import LowLevel.Types
import LowLevel.Syntax

-- | Encode a string appearing in a name.  Characters used by mangling are
-- replaced by a two-character string beginning with \'q\'.
encodeNameString :: String -> String
encodeNameString s = concatMap encodeLetter s
  where
    encodeLetter '_' = "qu"
    encodeLetter '.' = "qd"
    encodeLetter 'q' = "qq"
    encodeLetter c   = [c]

-- | Mangle a label.
mangleLabel :: Label -> String
mangleLabel name =
  "_pi_" ++
  encodeNameString (showModuleName $ moduleOf name) ++ "_" ++
  encodeNameString (labelUnqualifiedName name)

-- | Get a variable's mangled name.
--
-- If the variable has an exported name, then that variable is returned without
-- mangling.  If the variable has a label, then the variable's label and 
-- ID are used.
--
-- Otherwise, a single letter and the variable's ID are used.  This fallback
-- situation is susceptible to name conflicts, and should only be used for 
-- symbols that are not visible outside the current file.
mangledVarName :: Var -> String
mangledVarName v
  | Just s <- varExternalName v = s -- Use external name if given
  | varIsExternal v =
      case varName v
      of Just lab -> mangleLabel lab -- Mangle name, but don't add ID
         Nothing -> internalError $ "mangledVarName: External variables " ++
                                    "must have a label"
  | otherwise =
        case varName v
        of Just lab -> mangleLabel lab ++ "_" ++ mangled_id
           Nothing  -> type_leader (varType v) ++ mangled_id
  where
    mangled_id = show $ fromIdent $ varID v

    type_leader (PrimType t) =
      case t
      of PointerType -> "v_"
         OwnedType -> "v_"
         BoolType -> "b_"
         IntType Signed _ -> "i_"
         IntType Unsigned _ -> "u_"
         FloatType _ -> "f_"

    type_leader (RecordType _) = "r_"

