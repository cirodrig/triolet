
{-# LANGUAGE TemplateHaskell #-}
module LowLevel.InitializeBuiltins(initializeLowLevelBuiltins)
where
  
import Prelude hiding(catch)
import Control.Exception
import Control.Monad
import qualified Data.Map as Map
import Data.Maybe
import qualified Language.Haskell.TH as TH

import Common.Error
import Common.Identifier
import Common.Label
import Common.THRecord
import GlobalVar
import Globals
import LowLevel.Syntax
import LowLevel.CodeTypes
import LowLevel.BuiltinsTH
import LowLevel.Builtins
import LowLevel.Build
import LowLevel.FreshVar
import LowLevel.Print
import qualified Type.Environment
import Type.Type hiding(Var, runFreshVarM)
import qualified Type.Eval
import qualified Type.Var

-- This module helps us translate System F types into low-level types
import SystemF.Datatypes.Size(lowerGlobalFunctionType)
-- import {-# SOURCE #-} SystemF.Lowering.Datatypes2
import SystemF.Lowering.LowerMonad(LowerEnv, initializeLowerEnv)

fromBuiltinVarName :: BuiltinVarName -> (ModuleName, String, Maybe String)
fromBuiltinVarName (CName mod nm) = (mod, nm, Just nm)
fromBuiltinVarName (CoreName mod nm) = (mod, nm, Nothing)

initializePrimField :: IdentSupply Var -> BuiltinVarName -> FunctionType 
                    -> IO (Var, FunctionType)
initializePrimField supply name fty =
  runFreshVarM supply $ do
    let (mod, nm, ext_name) = fromBuiltinVarName name
        lab = externLabel mod nm [] ext_name
    v <- newExternalVar lab (PrimType PointerType)
    return (v, fty)

initializeClosureField :: IdentSupply Var 
                       -> BuiltinVarName 
                       -> FunctionType
                       -> IO (Var, EntryPoints)
initializeClosureField supply name fty = do
  when (not $ ftIsClosure fty) $ print "initializeClosureField: Error"
  runFreshVarM supply $ do
    let (mod, nm, ext_name) = fromBuiltinVarName name
        lab = externLabel mod nm [] ext_name
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
        lab = externLabel mod nm [] ext_name
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

lowerBuiltinFunType :: IdentSupply Var
                    -> IdentSupply Type.Var.Var
                    -> Type.Environment.TypeEnv
                    -> Type.Var.Var
                    -> IO FunctionType
lowerBuiltinFunType var_supply type_var_supply type_env con =
  Type.Environment.runTypeEvalM lower type_var_supply type_env `catch`
  \(exc :: SomeException) -> do
    putStrLn $ "Error while processing builtin '" ++ show con ++ "'"
    throwIO exc
  where
    lower = do
      m_type <- Type.Environment.lookupType con
      case m_type of
        Just ty -> lowerGlobalFunctionType var_supply ty
        Nothing -> internalError $
                   "lowerBuiltinFunType: Missing type for " ++ show con

lowerBuiltinObjType :: IdentSupply Type.Var.Var
                    -> Type.Environment.TypeEnv
                    -> Type.Var.Var
                    -> IO ValueType
lowerBuiltinObjType id_supply type_env var =
  Type.Environment.runTypeEvalM lower id_supply type_env
  where
    lower = do
      m_type <- Type.Environment.lookupType var
      case m_type of
        Just t -> do
          kind <- Type.Eval.typeKind t
          case kind of
            Type.Type.VarT kind
              | kind == Type.Type.boxV -> return $ PrimType OwnedType
              | kind == Type.Type.bareV -> return $ PrimType PointerType
            _ -> internalError $
                 "lowerBuiltinObjType: Incompatible representation for " ++ show var
        Nothing -> internalError $
                   "lowerBuiltinObjType: Missing type for " ++ show var
  
-- | Given an identifier supply, and the memory-annotated type environment,
--   initialize the builtin variables.
initializeLowLevelBuiltins :: IdentSupply Type.Var.Var
                           -> IdentSupply Var
                           -> Type.Environment.ITypeEnvBase Type.Environment.UnboxedMode
                           -> IO ()
initializeLowLevelBuiltins type_var_ids v_ids i_mem_type_env = do
  -- Create the environment needed for lowering
  mem_type_env <- Type.Environment.thawTypeEnv i_mem_type_env

  -- Create the record
  builtins_record <-
    $(
      let closure_type :: Either FunctionType TH.ExpQ -> TH.ExpQ
          -- Returns a quoted (IO FunctionType)
          closure_type (Left t) = [| return t |]
          closure_type (Right conQ) =
            [| lowerBuiltinFunType v_ids type_var_ids mem_type_env $conQ |]

          init_primitives =
            [("the_biprim_" ++ builtinVarUnqualifiedName nm,
              [| initializePrimField v_ids nm ty |]) 
            | (nm, ty) <- builtinPrimitives]
          init_functions =
            [("the_bifun_" ++ builtinVarUnqualifiedName nm,
              let mk_fty = closure_type ty
              in [| do fty <- $mk_fty
                       initializeClosureField v_ids nm fty |])
            | (nm, ty) <- builtinFunctions]
          init_globals =
            [("the_bivar_" ++ builtinVarUnqualifiedName nm,
              let mk_ty =
                    case src
                    of Left t -> [| return t |]
                       Right conQ -> 
                         [| lowerBuiltinObjType type_var_ids mem_type_env $conQ |]
              in [| do ty <- $mk_ty
                       initializeVarField v_ids nm ty |]) 
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
