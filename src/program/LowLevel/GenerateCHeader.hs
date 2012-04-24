{-| Generation of header files for exported C symbols.
-}

module LowLevel.GenerateCHeader(generateCHeader) where

import Data.Maybe

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Pretty
import Language.C.Syntax.AST
import Language.C.Syntax.Constants

import Common.Error
import Export
import LowLevel.Syntax
import LowLevel.GenerateCUtils

-- | Get the declaration components to use to declare a function parameter.
-- A parameter might occupy multiple C parameters, hence a list is returned.
exportParamDeclSpecs :: ExportDataType -> [DeclSpecs]
exportParamDeclSpecs export_type =
  case export_type
  of ListET False _ -> [ptrDeclSpecs $ nameDeclSpecs "PyonList"]
     ArrayET 2 False _ -> [ptrDeclSpecs $ nameDeclSpecs "PyonMatrix"]
     CSizeArrayET et ->
       case exportParamDeclSpecs et
       of [spec] -> [nameDeclSpecs "PyonInt", ptrDeclSpecs spec]
          _ ->
            -- Cannot make an array of something that isn't one parameter
            internalError "exportParamDeclSpecs"
     PyonNoneET -> []           -- NoneType parameters are removed
     PyonIntET -> [nameDeclSpecs "PyonInt"]
     PyonFloatET -> [nameDeclSpecs "PyonFloat"]
     PyonComplexFloatET -> [nameDeclSpecs "PyonComplexFloat"]
     PyonBoolET -> [nameDeclSpecs "PyonBool"]
     FunctionET _ _ -> [nameDeclSpecs "PyonClosure"]

-- | Get the declaration components to use to declare a function return type.
-- The return type might occupy parameters and/or the return value.  If there's
-- no return, the return type will be \"void\".
exportReturnDeclSpecs :: ExportDataType -> ([DeclSpecs], DeclSpecs)
exportReturnDeclSpecs export_type =
  case export_type
  of ListET False _ -> ([], ptrDeclSpecs $ nameDeclSpecs "PyonList")
     ArrayET 2 False _ -> ([], ptrDeclSpecs $ nameDeclSpecs "PyonMatrix")
     CSizeArrayET et -> 
       case exportParamDeclSpecs et
       of [spec] -> ([nameDeclSpecs "PyonInt"], ptrDeclSpecs spec)
          _ ->
            -- Cannot make an array of something that isn't one parameter
            internalError "exportReturnDeclSpecs"
     PyonNoneET -> ([], voidDeclSpecs)
     PyonIntET -> ([], nameDeclSpecs "PyonInt")
     PyonFloatET -> ([], nameDeclSpecs "PyonFloat")
     PyonComplexFloatET -> ([], nameDeclSpecs "PyonComplexFloat")
     PyonBoolET -> ([], nameDeclSpecs "PyonBool")
     FunctionET _ _ -> ([], nameDeclSpecs "PyonClosure")

-- | Get the declaration components to use to declare an exported function
exportSigDeclSpecs :: CSignature -> DeclSpecs
exportSigDeclSpecs (CSignature dom rng) =
  let dom_specs = map exportParamDeclSpecs dom
      (rng_param_specs, rng_ret_specs) = exportReturnDeclSpecs rng

      param_specs = concat dom_specs ++ rng_param_specs
      
      -- Create a derived function type from the return type
      fun_deriv =
        CFunDeclr (Right (map anonymousDecl param_specs, False)) [] internalNode

  in case rng_ret_specs
     of (rng_decl, rng_deriv) -> (rng_decl, fun_deriv : rng_deriv)

-- | Create a C external function declaration for the given variable, with the
-- given function signature.
generateExportDecl :: (Var, CSignature) -> CDecl
generateExportDecl (v, sig) =
  case exportSigDeclSpecs sig
  of (specs, derivs) ->
       let ident = varIdent v
           export_specs = CStorageSpec (CExtern internalNode) : specs
           declr = CDeclr (Just ident) derivs Nothing [] internalNode
       in CDecl export_specs [(Just declr, Nothing, Nothing)] internalNode

-- | Create the text of a C header file if there are any exported C functions
generateCHeader :: Module -> Maybe String
generateCHeader mod =
  let export_decls = [generateExportDecl (v, sig)
                     | (v, CExportSig sig) <- moduleExports mod]
      decls = map CDeclExt export_decls
      transl_module = CTranslUnit decls internalNode 
      header_body_text = show $ pretty transl_module
      header_text = cModuleHeader ++ header_body_text
  in if null export_decls
     then Nothing
     else Just header_text
     
cModuleHeader =
  "#include <inttypes.h>\n\
  \#include <pyon.h>\n"