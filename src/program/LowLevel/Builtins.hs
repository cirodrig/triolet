{-| Information about low-level builtin symbols.

This file contains a translation for every built-in variable that may be
lowered from System F, except for intrinsics which are in
"LowLevel.Intrinsics".
-}

{-# LANGUAGE TemplateHaskell #-}
module LowLevel.Builtins
       (-- * Built-in variables
        LowLevelBuiltins(..),
        the_lowLevelBuiltins,
        lowerBuiltinCoreFunction,
        allBuiltins,
        allBuiltinImports,
        llBuiltin,
        getBuiltinByLabel,
        getBuiltinImportByLabel,
        the_prim_exit,
        the_prim_triolet_alloc,
        the_prim_triolet_alloc_nopointers,
        the_prim_triolet_dealloc,
        the_prim_triolet_assert_nonnull_owned,
        the_prim_min_fii,
        the_prim_minus_fii,
        the_prim_apply_u_f,
        the_prim_apply_u,
        the_prim_apply_i32_f,
        the_prim_apply_i32,
        the_prim_apply_i64_f,
        the_prim_apply_i64,
        the_prim_apply_f32_f,
        the_prim_apply_f32,
        the_prim_apply_p_f,
        the_prim_apply_p,
        the_prim_apply_o_f,
        the_prim_apply_o,
        the_prim_apply_c_f,
        the_prim_apply_c,
        the_prim_force_Lazy,
        the_fun_putInt,
        the_fun_putUint,
        the_fun_putUintAsUint8,
        the_fun_putUintAsUint16,
        the_fun_putFloat,
        the_fun_putUnit,
        the_fun_putCursor,
        the_fun_putBoxedObject,
        the_fun_getInt,
        the_fun_getUint,
        the_fun_getUint8AsUint,
        the_fun_getUint16AsUint,
        the_fun_getFloat,
        the_fun_getUnit,
        the_fun_getCursor,
        the_fun_getBoxedObject,
        the_fun_updateDeserializationTable,
        the_fun_negate_int,
        the_fun_negate_float,
        the_fun_minus_ii,
        the_fun_min_ii,
        the_bivar_triolet_typeObject_function,
        {- the_fun_makeComplex,
        the_fun_load_int,
        the_fun_load_float,
        the_fun_load_NoneType,
        the_fun_store_int,
        the_fun_store_float,
        the_fun_store_NoneType,
        the_fun_additiveDict,
        the_fun_additiveDict_complex,
        the_fun_passConv_list,
        the_fun_complex_pass_conv,
        the_fun_AdditiveDict_pass_conv,
        the_fun_MultiplicativeDict_pass_conv,
        the_fun_list_vGenerate,
        the_bivar_OpaqueTraversableDict_list,
        the_bivar_passConv_int,
        the_bivar_float_pass_conv,
        the_bivar_bool_pass_conv,
        the_bivar_TraversableDict_pass_conv,
        the_bivar_PassConv_pass_conv -})
where

import Control.Monad
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Language.Haskell.TH as TH

import Common.Error
import Common.Identifier
import Common.THRecord
import Common.Label
import GlobalVar
import LowLevel.Syntax
import LowLevel.Types
import LowLevel.Record
import LowLevel.Records
import LowLevel.BuiltinsTH
import qualified Type.Var

type SFVar = Type.Var.Var

$(sequence [declareRecord lowLevelBuiltinsRecord])

-- Define field accessors
$(forM builtinFunctions $ \(fname, _) ->
   TH.funD (TH.mkName $ "the_fun_" ++ builtinVarUnqualifiedName fname) $
   let bi = return $ TH.VarE $ TH.mkName "builtins"
       fld = return $ TH.VarE $ TH.mkName $ "the_bifun_" ++ builtinVarUnqualifiedName fname
       read_from_field = TH.normalB [| fst ($(fld) $(bi)) |]
   in [TH.clause [TH.varP $ TH.mkName "builtins"] read_from_field []])

$(forM builtinPrimitives $ \(fname, _) ->
   TH.funD (TH.mkName $ "the_prim_" ++ builtinVarUnqualifiedName fname) $
   let bi = return $ TH.VarE $ TH.mkName "builtins"
       fld = return $ TH.VarE $ TH.mkName $ "the_biprim_" ++ builtinVarUnqualifiedName fname
       read_from_field = TH.normalB [| fst ($(fld) $(bi)) |]
   in [TH.clause [TH.varP $ TH.mkName "builtins"] read_from_field []])

-- | A list of all builtins
allBuiltins :: [Var]
allBuiltins =
  $(TH.listE $
    [ [| fst $ $(TH.varE $ TH.mkName $ builtinVarPrimName fname) lowLevelBuiltins |]
    | (fname, _) <- builtinPrimitives] ++
    [ [| fst $ $(TH.varE $ TH.mkName $ builtinVarFunName fname) lowLevelBuiltins |]
    | (fname, _) <- builtinFunctions] ++
    [ [| $(TH.varE $ TH.mkName $ builtinVarVarName fname) lowLevelBuiltins |]
    | (fname, _) <- builtinGlobals])

-- | A list of all builtin imports
allBuiltinImports :: [Import]
allBuiltinImports =
  $(TH.listE $
    [ [| let (v, t) = $(TH.varE $ TH.mkName $ builtinVarPrimName fname) lowLevelBuiltins 
         in ImportPrimFun v t Nothing |]
    | (fname, _) <- builtinPrimitives] ++
    [ [| let (v, ep) = $(TH.varE $ TH.mkName $ builtinVarFunName fname) lowLevelBuiltins
         in ImportClosureFun ep Nothing |]
    | (fname, _) <- builtinFunctions] ++
    [ [| let v = $(TH.varE $ TH.mkName $ builtinVarVarName fname) lowLevelBuiltins
         in ImportData v Nothing
       |]
    | (fname, _) <- builtinGlobals]
   )

-- | Get a builtin by field name
llBuiltin :: (LowLevelBuiltins -> a) -> a
llBuiltin f = f lowLevelBuiltins

-- | Get a builtin by its module and local name.
getBuiltinByLabel :: Label -> Maybe Var
getBuiltinByLabel s =
  fmap importVar $
  Map.lookup (labelModule s, labelLocalNameAsString s) builtinNameTable

-- | Get a builtin imported vaiable by its label
getBuiltinImportByLabel :: Label -> Maybe Import
getBuiltinImportByLabel s =
  Map.lookup (labelModule s, labelLocalNameAsString s) builtinNameTable

builtinNameTable :: Map.Map (ModuleName, String) Import
builtinNameTable =
  Map.fromList [(builtin_name $ importVar i, i) | i <- allBuiltinImports]
  where
    builtin_name v =
      case varName v
      of Just nm -> (labelModule nm, labelLocalNameAsString nm)
         Nothing -> internalError "builtinNameTable: Builtin variable has no name"

-- | All built-in functions that are produced by translating a constructor
builtinConTable =
  $(TH.listE [ TH.tupE [mk_con, TH.varE $ TH.mkName $ "the_fun_" ++ builtinVarUnqualifiedName fname]
             | (fname, Right mk_con) <- builtinFunctions])

-- | Get the low-level variable corresponding to a builtin function
-- constructor from core
lowerBuiltinCoreFunction :: SFVar -> Maybe Var
lowerBuiltinCoreFunction c = IntMap.lookup (fromIdent $ Type.Var.varID c) tbl
  where
    tbl = IntMap.fromList [ (fromIdent $ Type.Var.varID c, v lowLevelBuiltins)
                          | (c, v) <- builtinConTable]

-- | The low-level built-in global variables
the_lowLevelBuiltins :: InitGlobalVar LowLevelBuiltins
{-# NOINLINE lowLevelBuiltins #-}
the_lowLevelBuiltins = defineInitGlobalVar ()

lowLevelBuiltins :: LowLevelBuiltins
lowLevelBuiltins = readInitGlobalVar the_lowLevelBuiltins
