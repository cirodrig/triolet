
{-# LANGUAGE TemplateHaskell #-}
module LowLevel.InitializeBuiltins(initializeLowLevelBuiltins)
where
  
import qualified Data.Map as Map
import Data.Maybe
import qualified Language.Haskell.TH as TH

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.THRecord
import GlobalVar
import Globals
import LowLevel.Label
import LowLevel.Syntax
import LowLevel.CodeTypes
import LowLevel.BuiltinsTH
import LowLevel.Builtins
import LowLevel.Build
import LowLevel.FreshVar
import qualified Type.Environment
import Type.Type
import qualified Type.Var

-- This module helps us translate System F types into low-level types
import {-# SOURCE #-} SystemF.Lowering.Datatypes

fromBuiltinVarName :: BuiltinVarName -> (ModuleName, String, Maybe String)
fromBuiltinVarName (CName mod nm) = (mod, nm, Just nm)
fromBuiltinVarName (PyonName mod nm) = (mod, nm, Nothing)

initializePrimField :: IdentSupply Var -> BuiltinVarName -> FunctionType 
                    -> IO (Var, FunctionType)
initializePrimField supply name fty =
  runFreshVarM supply $ do
    let (mod, nm, ext_name) = fromBuiltinVarName name
        lab = externPyonLabel mod nm ext_name
    v <- newExternalVar lab (PrimType PointerType)
    return (v, fty)

initializeClosureField :: IdentSupply Var 
                       -> BuiltinVarName 
                       -> FunctionType
                       -> IO (Var, EntryPoints)
initializeClosureField supply name fty =
  runFreshVarM supply $ do
    let (mod, nm, ext_name) = fromBuiltinVarName name
        lab = externPyonLabel mod nm ext_name
    v <- newExternalVar lab (PrimType OwnedType)
    ep <- mkGlobalEntryPoints fty lab v
    return (v, ep)

initializeVarField :: IdentSupply Var 
                   -> BuiltinVarName
                   -> ValueType 
                   -> IO Var
initializeVarField supply name ty =
  runFreshVarM supply $ do
    let (mod, nm, ext_name) = fromBuiltinVarName name
        lab = externPyonLabel mod nm ext_name
    newExternalVar lab ty

{-
initializeGlobalField :: IdentSupply Var -> String -> ValueType -> IO Var
initializeGlobalField supply nm ty
  | typeOk ty =
      runFreshVarM supply $ do
        newBuiltinVar (builtinLabel nm) nm ty
  | otherwise =
      internalError "initializeGlobalField: unexpected type"
  where
    -- Global variables are used by reference, so they must have pointer type 
    -- or owned type
    typeOk (PrimType PointerType) = True
    typeOk (PrimType OwnedType) = True
    typeOk _ = False-}

lowerBuiltinFunType type_env con =
  case Type.Environment.lookupType con type_env
  of Just (BoxRT ::: ty) -> lowerFunctionType type_env ty
     Just _ -> internalError $
               "lowerBuiltinFunType: Incompatible representation for " ++ show con
     Nothing -> internalError $
                "lowerBuiltinFunType: Missing type for " ++ show con

  
-- | Given an identifier supply, and the memory-annotated type environment,
--   initialize the builtin variables.
initializeLowLevelBuiltins :: IdentSupply Var -> Type.Environment.TypeEnv -> IO ()
initializeLowLevelBuiltins v_ids mem_type_env = do
  -- Create the record
  builtins_record <-
    $(
      let closure_type :: Either FunctionType TH.ExpQ -> TH.ExpQ
          closure_type (Left t) = [| t |]
          closure_type (Right conQ) =
            [| lowerBuiltinFunType mem_type_env $conQ |]
          init_primitives =
            [("the_biprim_" ++ builtinVarUnqualifiedName nm,
              [| initializePrimField v_ids nm ty |]) 
            | (nm, ty) <- builtinPrimitives]
          init_functions =
            [("the_bifun_" ++ builtinVarUnqualifiedName nm,
              let fty = closure_type ty
              in [| initializeClosureField v_ids nm $fty |])
            | (nm, ty) <- builtinFunctions]
          init_globals =
            [("the_bivar_" ++ builtinVarUnqualifiedName nm,
              let ty = case src
                       of Left t -> t
                          Right _ -> PrimType PointerType -- All Pyon globals are referenced by pointer
              in [| initializeVarField v_ids nm ty |]) 
            | (nm, src) <- builtinGlobals]
          inits = init_primitives ++ init_functions ++ init_globals
      in initializeRecordM lowLevelBuiltinsRecord inits)

  -- Create a map from SystemF variable name to builtin variable name
  -- for all builtin functions
  let lowering_map =
        Map.fromList
        $(let bifun_assoc_entry (nm, Right varQ) =
                let name = TH.varE $ TH.mkName $ builtinVarFunName nm
                in Just [| ($varQ, fst ($name builtins_record)) |]
              bifun_assoc_entry (_, Left _) = Nothing
              
              bivar_assoc_entry (nm, Right varQ) =
                let name = TH.varE $ TH.mkName $ builtinVarVarName nm
                in Just [| ($varQ, $name builtins_record) |]
              bivar_assoc_entry (_, Left _) = Nothing
              
              assocs = mapMaybe bifun_assoc_entry builtinFunctions ++
                       mapMaybe bivar_assoc_entry builtinGlobals
          in TH.listE assocs)
  -- Save things to global variables
  initializeGlobalVar the_lowLevelBuiltins (return builtins_record)
  initializeGlobalVar the_loweringMap (return lowering_map)
