{-| Information about low-level builtin symbols.
-}

{-# LANGUAGE TemplateHaskell #-}
module Pyon.LowLevel.Builtins
       (LowLevelBuiltins,
        initializeLowLevelBuiltins,
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
        the_fun_store_NoneType,
        builtinType)
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
import Pyon.LowLevel.BuiltinsTH
import Pyon.LowLevel.FreshVar
import qualified Pyon.SystemF.Builtins as SystemF

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

llBuiltin :: (LowLevelBuiltins -> a) -> a
llBuiltin f = f lowLevelBuiltins

-- | Get the low-level type of a constructor
builtinType :: Con -> Maybe PrimType
builtinType c = IntMap.lookup (fromIdent $ conID c) builtinTypesTable

builtinTypesTable =
  IntMap.fromList [(fromIdent $ conID c, t) | (c, t) <- tbl]
  where
    tbl = []

initializePrimField :: IdentSupply Var -> String -> FunctionType 
                    -> IO (Var, FunctionType)
initializePrimField supply nm fty =
  runFreshVarM supply $ do
    let lab = builtinLabel nm
    v <- newBuiltinVar lab (PrimType PointerType)
    return (v, fty)

initializeClosureField :: IdentSupply Var -> String -> FunctionType
                       -> IO (Var, EntryPoints)
initializeClosureField supply nm fty =
  runFreshVarM supply $ do
    let lab = builtinLabel nm
    v <- newBuiltinVar lab (PrimType OwnedType)
    ep <- mkEntryPoints fty (Just lab)
    return (v, ep)

initializeVarField :: IdentSupply Var -> String -> ValueType -> IO Var
initializeVarField supply nm ty =
  runFreshVarM supply $ do
    newBuiltinVar (builtinLabel nm) ty

-- | The low-level built-in global variables
lowLevelBuiltins :: LowLevelBuiltins
lowLevelBuiltins = unsafePerformIO $ do
  whenM (isEmptyMVar lowLevelBuiltins_var) $
    internalError "Attempted to use 'lowLevelBuiltins' before initialization"

  readMVar lowLevelBuiltins_var

lowLevelBuiltins_var :: MVar LowLevelBuiltins
{-# NOINLINE lowLevelBuiltins_var #-}
lowLevelBuiltins_var = unsafePerformIO newEmptyMVar

initializeLowLevelBuiltins :: IdentSupply Var -> IO ()
initializeLowLevelBuiltins v_ids = do
  bi <- $(
    let init_primitives =
          [("the_biprim_" ++ nm, [| initializePrimField v_ids nm ty |]) 
          | (nm, ty) <- builtinPrimitives]
        init_functions =
          [("the_bifun_" ++ nm, [| initializeClosureField v_ids nm ty |])
          | (nm, ty) <- builtinFunctions]
        init_globals =
          [("the_bivar_" ++ nm, [| initializeVarField v_ids nm ty |]) 
          | (nm, ty) <- builtinGlobals]
        inits = init_primitives ++ init_functions ++ init_globals
    in initializeRecordM lowLevelBuiltinsRecord inits)
        
  ok <- tryPutMVar lowLevelBuiltins_var bi
  if ok then return ()
    else fail "initializeLowLevelBuiltins: Already initialized"
