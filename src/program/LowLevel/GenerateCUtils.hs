{-| Utilities for generating C output from low-level Pyon code.
-}

module LowLevel.GenerateCUtils where

import qualified Data.Set as Set

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Pretty
import Language.C.Syntax.AST
import Language.C.Syntax.Constants

import Common.Error
import Common.Label
import LowLevel.Syntax
import LowLevel.CodeTypes

-- | A C data type as encoded in an AST.  Types are divided into a specifier
-- and a derivation.
type DeclSpecs = ([CDeclSpec], [CDerivedDeclr])

-- | Create an anonymous declaration.  It can be used in a type cast or as
-- a function parameter.
anonymousDecl :: DeclSpecs -> CDecl
anonymousDecl (specs, deriv) =
  let declr = CDeclr Nothing deriv Nothing [] internalNode
  in CDecl specs [(Just declr, Nothing, Nothing)] internalNode

namedDecl :: DeclSpecs -> Ident -> CDecl
namedDecl (specs, deriv) name =
  let declr = CDeclr (Just name) deriv Nothing [] internalNode
  in CDecl specs [(Just declr, Nothing, Nothing)] internalNode

staticDeclSpecs :: DeclSpecs -> DeclSpecs
staticDeclSpecs (specs, derived) =
  (CStorageSpec (CStatic internalNode) : specs, derived)

funDeclSpecs :: [CDecl] -> DeclSpecs -> DeclSpecs
funDeclSpecs param_types (return_specs, return_derived_declr) =
  let fn_derived_declr = CFunDeclr (Right (param_types, False)) [] internalNode
  in (return_specs, fn_derived_declr : return_derived_declr)

typedefDeclSpecs :: DeclSpecs -> DeclSpecs
typedefDeclSpecs (specs, deriv) =
  (CStorageSpec (CTypedef internalNode) : specs, deriv)

nameDeclSpecs :: String -> DeclSpecs
nameDeclSpecs name = identDeclSpecs (internalIdent name)

identDeclSpecs :: Ident -> DeclSpecs
identDeclSpecs id = typeDeclSpecs (CTypeDef id internalNode)

typeDeclSpecs :: CTypeSpec -> DeclSpecs
typeDeclSpecs ts = ([CTypeSpec ts], [])

voidDeclSpecs :: DeclSpecs
voidDeclSpecs = typeDeclSpecs (CVoidType internalNode)

ptrDeclSpecs :: DeclSpecs -> DeclSpecs
ptrDeclSpecs (specs, deriv) = (specs, ptr : deriv)
  where
    ptr = CPtrDeclr [] internalNode

arrayDeclSpecs :: CExpr -> DeclSpecs -> DeclSpecs
arrayDeclSpecs size (base_type, base_deriv) =
  (base_type, CArrDeclr [] (CArrSize False size) internalNode : base_deriv)

-- | Create a structure type with the given field types.
--   The fields are named \'a\', \'b\', ....  The structure type has no name.
structDeclSpecs :: [DeclSpecs] -> DeclSpecs
structDeclSpecs field_types =
  let fields = zipWith namedDecl field_types field_names
      struct_type = CStruct CStructTag Nothing (Just fields) [] internalNode
      type_spec = CTypeSpec $ CSUType struct_type internalNode
  in ([type_spec], [])
  where
    field_names = map (internalIdent . return) ['a' .. 'z'] ++ too_many_fields
    too_many_fields = [internalError "structDeclSpecs: Too many fields"]

memoryPrimTypeDeclSpecs :: PrimType -> DeclSpecs
memoryPrimTypeDeclSpecs pt = primTypeDeclSpecs True pt

variablePrimTypeDeclSpecs :: PrimType -> DeclSpecs
variablePrimTypeDeclSpecs pt = primTypeDeclSpecs False pt

-- | Get the type specificer for a non-pointer primitive type.
--   'Bool' is represented by a different type in memory versus in a 
--   local variable.  The unit type cannot be represented in memory.
primTypeDeclSpecs :: Bool -> PrimType -> DeclSpecs
primTypeDeclSpecs is_memory pt =
  case pt
  of BoolType | is_memory -> typeDeclSpecs (CCharType internalNode)
              | otherwise -> typeDeclSpecs (CIntType internalNode)
     UnitType | is_memory -> internalError "primTypeDeclSpecs: Cannot represent a unit type stored in memory"
              | otherwise -> typeDeclSpecs (CIntType internalNode)
     IntType Signed S8 -> nameDeclSpecs "int8_t"
     IntType Signed S16 -> nameDeclSpecs "int16_t"
     IntType Signed S32 -> nameDeclSpecs "int32_t"
     IntType Signed S64 -> nameDeclSpecs "int64_t"
     IntType Unsigned S8 -> nameDeclSpecs "uint8_t"
     IntType Unsigned S16 -> nameDeclSpecs "uint16_t"
     IntType Unsigned S32 -> nameDeclSpecs "uint32_t"
     IntType Unsigned S64 -> nameDeclSpecs "uint64_t"
     FloatType S32 -> typeDeclSpecs (CFloatType internalNode)
     FloatType S64 -> typeDeclSpecs (CDoubleType internalNode)
     PointerType -> nameDeclSpecs "TrioletPtr"
     OwnedType -> internalError "primTypeDeclSpecs: Unexpected type"

varPrimType v = 
  case varType v
  of PrimType pt -> pt
     RecordType rec -> internalError "varPrimType: Unexpected record type"

-- | Generate the C name for an externally visible variable.
varIdent :: Var -> Ident
varIdent v = internalIdent $ mangledVarName False v

-- | Generate the C name for a local variable.
localVarIdent :: Var -> Ident
localVarIdent v = internalIdent $ mangledVarName True v

-- | Generate the long name if this variable is in the set, or the short
-- name otherwise.  The given set should be the set of global variables.
varIdentScoped :: Set.Set Var -> Var -> Ident
varIdentScoped gvars v
  | v `Set.member` gvars = varIdent v
  | otherwise            = localVarIdent v
