
{-# LANGUAGE TemplateHaskell #-}
module Untyped.Builtins2
       (BuiltinTyCon(..), builtinTyCon,
        BuiltinVar(..), builtinVar,
        initializeFrontendBuiltinTypes,
        initializeFrontendBuiltinVars,
        ParserVarBinding(..),
        predefinedBindings
       )
where

import Control.Concurrent.MVar
import Control.Monad
import Data.Array
import qualified Language.Haskell.TH as TH
import System.IO.Unsafe

import Common.Error
import Common.MonadLogic
import Untyped.BuiltinsTH2
import Untyped.Kind
import Untyped.Type
import Untyped.Variable

type FrontendBuiltinTypes = Array Int TyCon
type FrontendBuiltinVars  = Array Int Variable

$(do let cons = [tcName nm
                | nm <- frontendSourceTypes ++ frontendOtherTypes]
         con_decls = [return $ TH.NormalC c [] | c <- cons]

     -- Declare a data type
     data_decl <-
       TH.dataD (TH.cxt []) (TH.mkName "BuiltinTyCon") [] con_decls
       [TH.mkName "Enum", TH.mkName "Bounded", TH.mkName "Show"]

     return [data_decl])
         
$(do let cons = [vName nm
                | nm <- frontendSourceGlobals ++ frontendOtherGlobals]
         con_decls = [return $ TH.NormalC c [] | c <- cons]

     -- Declare a data type
     data_decl <-
       TH.dataD (TH.cxt []) (TH.mkName "BuiltinVar") [] con_decls
       [TH.mkName "Enum", TH.mkName "Bounded", TH.mkName "Show"]

     return [data_decl])

the_FrontendBuiltinTypes :: MVar FrontendBuiltinTypes
{-# NOINLINE the_FrontendBuiltinTypes #-}
the_FrontendBuiltinTypes = unsafePerformIO newEmptyMVar

the_FrontendBuiltinVars :: MVar FrontendBuiltinVars
{-# NOINLINE the_FrontendBuiltinVars #-}
the_FrontendBuiltinVars = unsafePerformIO newEmptyMVar

initializeFrontendBuiltinTypes :: [(BuiltinTyCon, TyCon)] -> IO ()
initializeFrontendBuiltinTypes tcs = do
  unlessM (isEmptyMVar the_FrontendBuiltinTypes) $
    internalError "initializeFrontendBuiltinTypes: Already initialized"
  putMVar the_FrontendBuiltinTypes arr
  where
    empty_arr = listArray (lb, ub) [err tc | tc <- [minBound .. maxBound]]
    arr = accum (const id) empty_arr [ (fromEnum i, c) | (i, c) <- tcs]
    lb = fromEnum (minBound :: BuiltinTyCon)
    ub = fromEnum (maxBound :: BuiltinTyCon)
    err :: BuiltinTyCon -> a
    err tc = internalError $ "Frontend builtin type constructor is uninitialized: " ++ show tc

initializeFrontendBuiltinVars :: [(BuiltinVar, Variable)] -> IO ()
initializeFrontendBuiltinVars vs = do
  unlessM (isEmptyMVar the_FrontendBuiltinVars) $
    internalError "initializeFrontendBuiltinTypes: Already initialized"
  putMVar the_FrontendBuiltinVars arr
  where
    empty_arr = listArray (lb, ub) [err tc | tc <- [minBound .. maxBound]]
    arr = accum (const id) empty_arr [ (fromEnum i, c) | (i, c) <- vs]
    lb = fromEnum (minBound :: BuiltinVar)
    ub = fromEnum (maxBound :: BuiltinVar)
    err :: BuiltinVar -> a
    err tc = internalError $ "Frontend builtin variable is uninitialized: " ++ show tc

builtinTyCon :: BuiltinTyCon -> TyCon
{-# INLINE builtinTyCon #-}
builtinTyCon field = builtinTyCon' (fromEnum field)

builtinTyCon' field_index = field_index `seq` unsafePerformIO get_value
  where
    get_value = do
      -- Ensure that we've already initialized these
      bi_is_empty <- isEmptyMVar the_FrontendBuiltinTypes
      when bi_is_empty $ internalError "Frontend builtins are uninitialized"
      
      -- Load and return the desired field
      bi <- readMVar the_FrontendBuiltinTypes
      return $! bi ! field_index

builtinVar :: BuiltinVar -> Variable
{-# INLINE builtinVar #-}
builtinVar field = builtinVar' (fromEnum field)

builtinVar' field_index = field_index `seq` unsafePerformIO get_value
  where
    get_value = do
      -- Ensure that we've already initialized these
      bi_is_empty <- isEmptyMVar the_FrontendBuiltinVars
      when bi_is_empty $ internalError "Frontend builtins are uninitialized"
      
      -- Load and return the desired field
      bi <- readMVar the_FrontendBuiltinVars
      return $! bi ! field_index

-------------------------------------------------------------------------------

-- | The value bound to a variable in the parser.
--
-- Variables in source code may represent a kind, type, or object-level term. 
--
-- Kinds and types cannot be defined in source code, but some are predefined.
-- Type variables can be defined in source code.
data ParserVarBinding =
    KindBinding !Kind
  | TypeBinding !TyCon
  | ObjectBinding !Variable

-- | Predefined names that may be referenced in source code.
predefinedBindings :: [(String, ParserVarBinding)]
predefinedBindings = kind_bindings ++ type_bindings ++ var_bindings
  where
    kind_bindings = [("type", KindBinding Star)]
    type_bindings =
      $(TH.listE [ [| (t, TypeBinding $ builtinTyCon $(TH.conE $ tcName t)) |]
                 | t <- frontendSourceTypes])
    var_bindings =
      $(TH.listE [ [| (t, ObjectBinding $ builtinVar $(TH.conE $ vName t)) |]
                 | t <- frontendSourceGlobals])
