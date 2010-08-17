{-| Information about low-level builtin symbols.
-}

{-# LANGUAGE TemplateHaskell #-}
module LowLevel.Builtins
       (-- * Record types
        passConvRecord,

        -- * Built-in variables
        LowLevelBuiltins(..),
        the_lowLevelBuiltins,
        lowerBuiltinCoreFunction,
        allBuiltins,
        llBuiltin,
        getBuiltinByName,
        the_prim_pyon_alloc,
        the_prim_pyon_dealloc,
        the_prim_apply_i32_f,
        the_prim_apply_i32,
        the_prim_apply_f32_f,
        the_prim_apply_f32,
        the_prim_free_pap,
        the_fun_add_int,
        the_fun_sub_int,
        the_fun_add_float,
        the_fun_sub_float,
        the_fun_dummy_finalizer,
        the_fun_copy1F,
        the_fun_copy2F,
        the_fun_copy4F,
        the_fun_load_int,
        the_fun_load_float,
        the_fun_load_NoneType,
        the_fun_store_int,
        the_fun_store_float,
        the_fun_store_NoneType)
where

import Control.Monad
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Language.Haskell.TH as TH

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.THRecord
import Gluon.Core(Con(..))
import GlobalVar
import LowLevel.Syntax
import LowLevel.Types
import LowLevel.Record
import LowLevel.Records
import LowLevel.BuiltinsTH

$(sequence [declareRecord lowLevelBuiltinsRecord])

-- Define field accessors
$(forM builtinFunctions $ \(fname, _) ->
   TH.funD (TH.mkName $ "the_fun_" ++ fname) $
   let bi = return $ TH.VarE $ TH.mkName "builtins"
       fld = return $ TH.VarE $ TH.mkName $ "the_bifun_" ++ fname
       read_from_field = TH.normalB [| fst ($(fld) $(bi)) |]
   in [TH.clause [TH.varP $ TH.mkName "builtins"] read_from_field []])

$(forM builtinPrimitives $ \(fname, _) ->
   TH.funD (TH.mkName $ "the_prim_" ++ fname) $
   let bi = return $ TH.VarE $ TH.mkName "builtins"
       fld = return $ TH.VarE $ TH.mkName $ "the_biprim_" ++ fname
       read_from_field = TH.normalB [| fst ($(fld) $(bi)) |]
   in [TH.clause [TH.varP $ TH.mkName "builtins"] read_from_field []])

-- | A list of all builtins
allBuiltins :: [Var]
allBuiltins =
  $(TH.listE $ [ [| fst $ $(TH.varE $ TH.mkName $ "the_biprim_" ++ fname) lowLevelBuiltins |]
               | (fname, _) <- builtinPrimitives] ++
               [ [| fst $ $(TH.varE $ TH.mkName $ "the_bifun_" ++ fname) lowLevelBuiltins |]
               | (fname, _) <- builtinFunctions] ++
               [ [| $(TH.varE $ TH.mkName $ "the_bivar_" ++ fname) lowLevelBuiltins |]
               | (fname, _) <- builtinGlobals])

-- | Get a builtin by field name
llBuiltin :: (LowLevelBuiltins -> a) -> a
llBuiltin f = f lowLevelBuiltins

-- | Get a builtin by its program name
getBuiltinByName :: String -> Maybe Var
getBuiltinByName s = Map.lookup s builtinNameTable

builtinNameTable = Map.fromList [(builtin_name b, b) | b <- allBuiltins]
  where
    builtin_name v =
      case varName v
      of Just nm -> labelUnqualifiedName nm
         Nothing -> internalError "builtinNameTable: Builtin variable has no name"

-- | All built-in functions that are produced by translating a constructor
builtinConTable =
  $(TH.listE [ TH.tupE [mk_con, TH.varE $ TH.mkName $ "the_fun_" ++ fname]
             | (fname, Right mk_con) <- builtinFunctions])

-- | Get the low-level variable corresponding to a builtin function
-- constructor from core
lowerBuiltinCoreFunction :: Con -> Maybe Var
lowerBuiltinCoreFunction c = IntMap.lookup (fromIdent $ conID c) tbl
  where
    tbl = IntMap.fromList [ (fromIdent $ conID c, v lowLevelBuiltins)
                          | (c, v) <- builtinConTable]

-- | The low-level built-in global variables
the_lowLevelBuiltins :: InitGlobalVar LowLevelBuiltins
{-# NOINLINE lowLevelBuiltins #-}
the_lowLevelBuiltins = defineInitGlobalVar ()

lowLevelBuiltins :: LowLevelBuiltins
lowLevelBuiltins = readInitGlobalVar the_lowLevelBuiltins

