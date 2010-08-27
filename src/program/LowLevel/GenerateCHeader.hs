{-| Generation of header files for exported C symbols.
-}

module LowLevel.GenerateCHeader(generateCHeader) where

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Pretty
import Language.C.Syntax.AST
import Language.C.Syntax.Constants

import Gluon.Common.Error
import Export
import LowLevel.Syntax
import LowLevel.GenerateCUtils

-- | Get the declaration components to use to declare a function parameter.
-- A parameter might occupy multiple C parameters, hence a list is returned.
exportParamDeclSpecs :: ExportDataType -> [DeclSpecs]
exportParamDeclSpecs export_type =
  case export_type
  of ListET _ -> [ptrDeclSpecs $ nameDeclSpecs "PyonList"]
     CSizeArrayET et ->
       case exportParamDeclSpecs et
       of [spec] -> [nameDeclSpecs "PyonInt", ptrDeclSpecs spec]
          _ ->
            -- Cannot make an array of something that isn't one parameter
            internalError "exportParamDeclSpecs"
     PyonIntET -> [nameDeclSpecs "PyonInt"]
     PyonFloatET -> [nameDeclSpecs "PyonFloat"]
     PyonBoolET -> [nameDeclSpecs "PyonBool"]

-- | Get the declaration components to use to declare a function return type.
-- The return type might occupy parameters and/or the return value.  If there's
-- no return, the return type will be \"void\".
exportReturnDeclSpecs :: ExportDataType -> ([DeclSpecs], DeclSpecs)
exportReturnDeclSpecs export_type =
  case export_type
  of ListET _ -> ([], ptrDeclSpecs $ nameDeclSpecs "PyonList")
     CSizeArrayET et -> 
       case exportParamDeclSpecs et
       of [spec] -> ([nameDeclSpecs "PyonInt"], ptrDeclSpecs spec)
          _ ->
            -- Cannot make an array of something that isn't one parameter
            internalError "exportReturnDeclSpecs"
     PyonIntET -> ([], nameDeclSpecs "PyonInt")
     PyonFloatET -> ([], nameDeclSpecs "PyonFloat")
     PyonBoolET -> ([], nameDeclSpecs "PyonBool")

-- | Get the declaration components to use to declare an exported function
exportSigDeclSpecs :: ExportSig -> DeclSpecs
exportSigDeclSpecs (ExportSig dom rng) =
  let dom_specs = map exportParamDeclSpecs dom
      (rng_param_specs, rng_ret_specs) = exportReturnDeclSpecs rng

      param_specs = concat dom_specs ++ rng_param_specs
      
      -- Create a derived function type from the return type
      fun_deriv =
        CFunDeclr (Right (map anonymousDecl param_specs, False)) [] internalNode

  in case rng_ret_specs
     of (rng_decl, rng_deriv) -> (rng_decl, fun_deriv : rng_deriv)

-- | Create an external function declaration for the given variable, with the
-- given function signature.
generateExportDecl :: (Var, ExportSig) -> CDecl
generateExportDecl (v, sig) =
  let (specs, derivs) = exportSigDeclSpecs sig
      ident = varIdent v
      export_specs = CStorageSpec (CExtern internalNode) : specs
      declr = CDeclr (Just ident) derivs Nothing [] internalNode
  in CDecl export_specs [(Just declr, Nothing, Nothing)] internalNode

generateCHeader :: Module -> String
generateCHeader mod =
  let export_decls = map generateExportDecl $ moduleExports mod
      decls = map CDeclExt export_decls
      transl_module = CTranslUnit decls internalNode 
      header_body_text = show $ pretty transl_module
  in cModuleHeader ++ header_body_text
     
cModuleHeader =
  "#include <inttypes.h>\n\
  \#include <pyon.h>\n"