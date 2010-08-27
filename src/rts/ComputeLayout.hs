{-| This program generates a C header file containing data structure 
-- layout information.
-}

import Data.List
import System.Environment

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
typeName (RecordField _) = error "Unflattened record"
typeName (AlignField _)  = error "Unexpected alignment field"
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

defineRecord :: StaticRecord -> String -> [String] -> ShowS
defineRecord rec rec_name field_names
  | length field_names /= length (recordFields $ flattenStaticRecord rec) =
      error $
      "Numbers of fields and field names do not match in record " ++ rec_name
  | otherwise =
      let field_strings = map showString field_names
          define_offset = defineOffset (showString rec_name)
          flat_fields = recordFields $ flattenStaticRecord rec
          record_size = defineMacro (showString ("SIZEOF_" ++ rec_name)) $
                        shows (sizeOf rec)
      in vcat $ record_size : zipWith define_offset field_strings flat_fields

defineTypeTag :: String -> TypeTag -> ShowS
defineTypeTag name tag =
  defineMacro (showString name) (shows $ fromEnum tag)

defineBitsTag :: String -> BitsTag -> ShowS
defineBitsTag name tag =
  defineMacro (showString name) (shows $ fromEnum tag)

defineInfoTag :: String -> InfoTag -> ShowS
defineInfoTag name tag =
  defineMacro (showString name) (shows $ fromEnum tag)

defineSizeAlign :: HasSize a => String -> a -> ShowS
defineSizeAlign name x =
  let sizeof_name = showString ("SIZEOF_" ++ name)
      alignof_name = showString ("ALIGNOF_" ++ name)
  in defineMacro sizeof_name (shows $ sizeOf x) . showChar '\n' .
     defineMacro alignof_name (shows $ alignOf x)

defineAll = vcat
  [ defineRecord infoTableHeaderRecord "INFO"
    ["FREE", "TAG"]
  , defineRecord funInfoHeaderRecord "FUNINFO"
    ["FREE", "TAG", "ARITY", "EXACT", "INEXACT"]
  , defineRecord objectHeaderRecord "OBJECT"
    ["REFCT", "INFO"]
  , defineRecord papHeaderRecord "PAP"
    ["REFCT", "INFO", "FUN", "NARGUMENTS"]
  , defineRecord passConvRecord "PASSCONV"
    ["SIZE", "ALIGN", "COPY", "FINI"]
  , defineTypeTag "INT8_TAG" Int8Tag
  , defineTypeTag "INT16_TAG" Int16Tag
  , defineTypeTag "INT32_TAG" Int32Tag
  , defineTypeTag "INT64_TAG" Int64Tag
  , defineTypeTag "FLOAT32_TAG" Float32Tag
  , defineTypeTag "FLOAT64_TAG" Float64Tag
  , defineTypeTag "OWNEDREF_TAG" OwnedRefTag
  , defineBitsTag "BITS_32_TAG" Bits32Tag
  , defineBitsTag "BITS_64_TAG" Bits64Tag
  , defineBitsTag "OWNED_REF_BITS_TAG" OwnedRefBitsTag
  , defineInfoTag "FUN_TAG" FunTag
  , defineInfoTag "PAP_TAG" PAPTag
  , defineSizeAlign "PYON_PTR" PointerType
  , defineSizeAlign "PYON_INT" pyonIntType
  , defineSizeAlign "PYON_FLOAT" pyonFloatType
  , defineMacro (showString "MAX_SCALAR_ALIGNMENT") (shows maxScalarAlignment) 
  , defineMacro (showString "DYN_SCALAR_ALIGNMENT") (shows dynamicScalarAlignment)
 ]

writeLayoutFile layout_filename =
  let layout_contents =
        showString "#ifndef _LAYOUT_H\n" .
        showString "#define _LAYOUT_H\n" .
        defineAll .
        showString "\n#endif\n"
  in writeFile layout_filename $ layout_contents ""

writeTypesFile types_filename =
  let (word_type, int_type) =
        case pyonIntSize 
        of S32 -> ("uint32_t", "int32_t")
           S64 -> ("uint64_t", "int64_t")
      float_type =
        case pyonFloatSize
        of S32 -> "float"
           S64 -> "double"
      bool_type =
        case nativeIntSize
        of S32 -> "int32_t"
           S64 -> "int64_t"

      types_contents =
        "#ifndef _PYON_TYPES_H\n" ++
        "#define _PYON_TYPES_H\n" ++
        "#include <inttypes.h>\n" ++
        "typedef void *PyonPtr;\n" ++
        "typedef " ++ int_type ++ " PyonInt;\n" ++
        "typedef " ++ word_type ++ " PyonWord;\n" ++
        "typedef " ++ float_type ++ " PyonFloat;\n" ++
        "typedef " ++ bool_type ++ " PyonBool;\n" ++
        "#endif"
  in writeFile types_filename types_contents

main = do
  [layout_filename, types_filename] <- getArgs
  
  writeLayoutFile layout_filename
  writeTypesFile types_filename
  
