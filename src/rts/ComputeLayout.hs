{-| This program generates a C header file containing data structure 
-- layout information.
-}

import Data.List

import LowLevel.Types
import LowLevel.Record
import LowLevel.Records

-- | Show in parentheses
parens :: ShowS -> ShowS
parens s = showChar '(' . s . showChar ')'

-- | Concatenate 
cat :: [ShowS] -> ShowS
cat = foldr (.) id

-- | Concatenate on separate lines
vcat :: [ShowS] -> ShowS
vcat = cat . intersperse (showChar '\n')

-- | Create a C name representing a type
typeName :: StaticFieldType -> ShowS
typeName (RecordField _ _) = showString "PyonPtr"
typeName (PrimField ty) = showString $
  case ty
  of BoolType             -> "uint8_t"
     IntType Signed S8    -> "int8_t"
     IntType Signed S16   -> "int16_t"
     IntType Signed S32   -> "int32_t"
     IntType Signed S64   -> "int64_t"
     IntType Unsigned S8  -> "uint8_t"
     IntType Unsigned S16 -> "uint16_t"
     IntType Unsigned S32 -> "uint32_t"
     IntType Unsigned S64 -> "uint64_t"
     FloatType S32        -> "float"
     FloatType S64        -> "double"
     PointerType          -> "PyonPtr"
     OwnedType            -> "PyonPtr"
     _ -> error "Unrecognized type" 

-- | Create a CPP macro
defineMacro :: ShowS -> ShowS -> ShowS
defineMacro proto subst =
  showString "#define " . proto . showChar ' ' . subst

-- #define STRUCT_FIELD(ptr) (*(TYPE *)((char *)(ptr) + offset))
defineOffset :: ShowS -> ShowS -> StaticField -> ShowS
defineOffset struct_name field_name field =
  let macro_name = struct_name . showChar '_' . field_name
      offset = fieldOffset field
      cast = parens $
             showChar '*' .
             parens (typeName (fieldType field) . showChar '*') .
             parens (showString "(char *)(ptr) + " . shows offset)
  in defineMacro (macro_name . showString "(ptr)") cast

defineRecordOffsets :: StaticRecord -> String -> [String] -> ShowS
defineRecordOffsets rec rec_name field_names
  | length field_names /= length (recordFields rec) =
      error "Numbers of fields and field names do not match"
  | otherwise =
      let field_strings = map showString field_names
          define_offset = defineOffset (showString rec_name)
      in vcat $ zipWith define_offset field_strings (recordFields rec) 

defineTypeTag :: String -> TypeTag -> ShowS
defineTypeTag name tag =
  defineMacro (showString name) (shows $ fromEnum tag)

defineInfoTag :: String -> InfoTag -> ShowS
defineInfoTag name tag =
  defineMacro (showString name) (shows $ fromEnum tag)

defineAll = vcat
  [ defineRecordOffsets infoTableHeaderRecord "INFO"
    ["FREE", "TAG"]
  , defineRecordOffsets funInfoHeaderRecord "FUNINFO"
    ["FREE", "TAG", "ARITY", "NCAPTURED", "NRECURSIVE", "EXACT", "INEXACT"]
  , defineRecordOffsets objectHeaderRecord "OBJECT"
    ["REFCT", "INFO"]
  , defineRecordOffsets papHeaderRecord "PAP"
    ["REFCT", "INFO", "FUN", "NARGUMENTS"]
  , defineTypeTag "INT8_TAG" Int8Tag
  , defineTypeTag "INT16_TAG" Int16Tag
  , defineTypeTag "INT32_TAG" Int32Tag
  , defineTypeTag "INT64_TAG" Int64Tag
  , defineTypeTag "FLOAT32_TAG" Float32Tag
  , defineTypeTag "FLOAT64_TAG" Float64Tag
  , defineTypeTag "OWNEDREF_TAG" OwnedRefTag
  , defineInfoTag "FUN_TAG" FunTag
  , defineInfoTag "PAP_TAG" PAPTag
  , defineMacro (showString "SIZEOF_PYONPTR") (shows $ sizeOf PointerType)
  , defineMacro (showString "ALIGNOF_PYONPTR") (shows $ alignOf PointerType)
  ]

main = do
  putStrLn "#ifndef _LAYOUT_H"
  putStrLn "#define _LAYOUT_H"
  putStrLn (defineAll "")
  putStrLn "#endif"
