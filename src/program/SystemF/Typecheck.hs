
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, EmptyDataDecls,
             FlexibleInstances, DeriveDataTypeable, TypeSynonymInstances #-}
module SystemF.Typecheck where

import Control.Applicative(Const(..))
import Control.Exception
import Control.Monad
import Control.Monad.Reader
import Data.Typeable(Typeable)
import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import Common.SourcePos

import GlobalVar
import Globals
import SystemF.Print
import SystemF.Syntax
import Builtins.Builtins
import Type.Eval
import Type.Environment
import Type.Type
import Type.Rename
import Type.Compare

withMany :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c
withMany f xs k = go xs k
  where
    go (x:xs) k = f x $ \y -> go xs $ \ys -> k (y:ys)
    go []     k = k []

-- | Set to True for debugging
printTypeAssertions :: Bool
printTypeAssertions = False

data Typed s deriving(Typeable)

-------------------------------------------------------------------------------
-- Type-checking environment

data TCEnv = TCEnv 
             { tcVarIDSupply :: !(IdentSupply Var)
             , tcTypeEnv     :: TypeEnv
             }

type TCM a = ReaderT TCEnv IO a

typeError = error

assume :: Var -> ReturnRepr ::: Type -> TCM a -> TCM a 
assume v t m = local add_to_env m
  where
    add_to_env env = env {tcTypeEnv = insertType v t $ tcTypeEnv env}

lookupVar :: Var -> TCM ReturnType
lookupVar v = do
  env <- asks tcTypeEnv
  case lookupType v env of
    Just rt -> return rt
    Nothing -> internalError $ "lookupVar: No type for variable: " ++ show v

tcLookupDataCon :: Var -> TCM DataConType
tcLookupDataCon v = do
  env <- asks tcTypeEnv
  case lookupDataCon v env of
    Just dct -> return dct
    Nothing -> internalError $ "lookupVar: No type for data constructor: " ++ show v

checkType :: SourcePos -> Type -> Type -> TCM Bool
checkType pos expected given = ReaderT $ \env -> do
  compareTypes (tcVarIDSupply env) (tcTypeEnv env) expected given

checkReturnType :: SourcePos -> ReturnType -> ReturnType -> TCM Bool
checkReturnType pos (erepr ::: etype) (grepr ::: gtype)
  | sameReturnRepr erepr grepr = checkType pos etype gtype
  | otherwise = return False

applyType :: Type -> ReturnType -> Maybe Type -> TCM (Maybe ReturnType)
applyType op_type arg_type arg = ReaderT $ \env -> do
  applied <- typeOfApp (tcVarIDSupply env) (tcTypeEnv env)
             op_type arg_type arg
  return applied

checkLiteralType :: Lit -> TCM ()
checkLiteralType l =
  if isValidLiteralType (literalType l) l
  then return ()
  else typeError "Not a valid literal type"
  where
    isValidLiteralType ty lit =
      -- Get the type constructor
      case fromVarApp ty
      of Just (v, args) ->
           -- Based on the literal, check whether the type constructor is 
           -- acceptable
           case lit
           of IntL _ _ -> v `isPyonBuiltin` the_int
              FloatL _ _ -> v `isPyonBuiltin` the_float
         Nothing ->
           -- Literals cannot have other types 
           False

-- | Instantiate a data constructor's type in a pattern, given the
--   pattern's type arguments.
--   Verify that the argument type kinds and existental type kinds are correct.
instantiatePatternType :: SourcePos -- ^ Position where pattern was mentioned
                       -> DataConType    -- ^ Constructor to instantiate
                       -> [(Type, Type)] -- ^ Each type argument and its kind
                       -> [(Var, Type)]  -- ^ Each existential variable and its kind
                       -> TCM ([ParamType], [ReturnType], ReturnType)
                       -- ^ Compute field types and range type
instantiatePatternType pos con_ty arg_vals ex_vars
  | length (dataConPatternParams con_ty) /= length arg_vals =
      internalError "instantiatePatternType: Wrong number of type parameters"
  | length (dataConPatternExTypes con_ty) /= length ex_vars =
      internalError "instantiatePatternType: Wrong number of existential variables"
  | otherwise = do
      -- Check argument types
      zipWithM_ check_argument_type (dataConPatternParams con_ty) arg_vals
      
      -- Check existential types
      zipWithM_ check_ex_pattern (dataConPatternExTypes con_ty) ex_vars

      -- Instantiate the type
      return $
        instantiateDataConType con_ty (map fst arg_vals) (map fst ex_vars)
  where
    check_argument_type (_ ::: expected_type) (_, given_type) =
      checkType pos expected_type given_type
      
    check_ex_pattern (_ ::: expected_type) (_, given_type) =
      checkType pos expected_type given_type
