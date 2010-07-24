{-| Information about low-level builtin symbols.
-}

{-# LANGUAGE TemplateHaskell #-}
module Pyon.LowLevel.Builtins
       (-- * Record types
        passConvRecord,

        -- * Built-in variables
        LowLevelBuiltins(..),
        lowLevelBuiltins_var,
        lowerBuiltinCoreFunction,
        allBuiltins,
        llBuiltin,
        the_prim_alloc,
        the_prim_dealloc,
        the_prim_apply_pap,
        the_prim_free_pap,
        the_prim_free_lambda_closure,
        the_prim_free_letrec_closure,
        the_fun_add_int,
        the_fun_sub_int,
        the_fun_add_float,
        the_fun_sub_float,
        the_fun_dealloc,
        the_fun_copy4,
        the_fun_load_int,
        the_fun_load_float,
        the_fun_load_NoneType,
        the_fun_store_int,
        the_fun_store_float,
        the_fun_store_NoneType)
where

import Control.Concurrent.MVar
import Control.Monad
import qualified Data.IntMap as IntMap
import Debug.Trace
import qualified Language.Haskell.TH as TH
import System.IO.Unsafe

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.MonadLogic
import Gluon.Common.THRecord
import Gluon.Core(Con(..))
import Pyon.LowLevel.Syntax
import Pyon.LowLevel.Types
import Pyon.LowLevel.Record
import Pyon.LowLevel.BuiltinsTH
import Pyon.LowLevel.FreshVar

-------------------------------------------------------------------------------
-- Record types

-- | A parameter passing convention consists of size, alignment, copy,
-- and free functions
passConvRecord :: StaticRecord
passConvRecord = staticRecord [ PrimField nativeWordType
                              , PrimField nativeWordType
                              , PrimField OwnedType
                              , PrimField OwnedType
                              ]

-------------------------------------------------------------------------------

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

-- | Get a builtin by name
llBuiltin :: (LowLevelBuiltins -> a) -> a
llBuiltin f = f lowLevelBuiltins

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
lowLevelBuiltins :: LowLevelBuiltins
lowLevelBuiltins = unsafePerformIO $ do
  whenM (isEmptyMVar lowLevelBuiltins_var) $
    internalError "Attempted to use 'lowLevelBuiltins' before initialization"

  readMVar lowLevelBuiltins_var

lowLevelBuiltins_var :: MVar LowLevelBuiltins
{-# NOINLINE lowLevelBuiltins_var #-}
lowLevelBuiltins_var = unsafePerformIO newEmptyMVar
