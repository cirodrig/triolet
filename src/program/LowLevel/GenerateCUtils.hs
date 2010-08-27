{-| Utilities for generating C output from low-level Pyon code.
-}

module LowLevel.GenerateCUtils where

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Pretty
import Language.C.Syntax.AST
import Language.C.Syntax.Constants

import Gluon.Common.Error
import LowLevel.Label
import LowLevel.Syntax
import LowLevel.Types

-- | A C data type as encoded in an AST.  Types are divided into a specifier
-- and a derivation.
type DeclSpecs = ([CDeclSpec], [CDerivedDeclr])

-- | Create an anonymous declaration.  It can be used in a type cast or as
-- a function parameter.
anonymousDecl :: DeclSpecs -> CDecl
anonymousDecl (specs, deriv) =
  let declr = CDeclr Nothing deriv Nothing [] internalNode
  in CDecl specs [(Just declr, Nothing, Nothing)] internalNode

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

-- | Get the type specificer for a non-pointer primitive type
primTypeDeclSpecs :: PrimType -> DeclSpecs
primTypeDeclSpecs pt =
  case pt
  of BoolType -> typeDeclSpecs (CIntType internalNode)
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
     PointerType -> nameDeclSpecs "PyonPtr"


varPrimType v = valueToPrimType $ varType v

-- | Generate the C name for a variable.
-- If it's a builtin variable, or if it's an exported
-- variable, then use the name alone.  Otherwise, generate a unique name
-- using the variable's name and ID.
varIdent :: Var -> Ident
varIdent v = internalIdent $ mangledVarName v

