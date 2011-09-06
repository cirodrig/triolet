
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

-- | A type-annotated thing
data TypeAnn a =
  TypeAnn { typeAnnotation :: Type
          , typeAnnValue :: a
          }

instance Functor TypeAnn where
  fmap f (TypeAnn t x) = TypeAnn t (f x)

class HasType a where getTypeAnn :: a -> Type

-------------------------------------------------------------------------------
-- Type-checking environment

-- | The type-checking monad
type TCM a = TypeEvalM a

typeError = error

lookupVar :: Var -> TCM Type
lookupVar v = do
  env <- getTypeEnv
  case lookupType v env of
    Just rt -> return rt
    Nothing -> internalError $ "lookupVar: No type for variable: " ++ show v

tcLookupDataCon :: Var -> TCM DataConType
tcLookupDataCon v = do
  env <- getTypeEnv
  case lookupDataCon v env of
    Just dct -> return dct
    Nothing -> internalError $ "lookupVar: No type for data constructor: " ++ show v

-- | Throw an error if the given types do not match
checkType :: Doc -> SourcePos -> Type -> Type -> TCM ()
checkType message pos expected given = compareTypes expected given >>= ck
  where
    error_message = "Type error at " ++ show pos ++ ":\n" ++ show message

    ck True  = return ()
    ck False = typeError error_message

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
           of IntL _ _ -> v `isPyonBuiltin` The_int
              FloatL _ _ -> v `isPyonBuiltin` The_float
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
                       -> TCM ([Binder], [Type], Type)
                       -- ^ Compute field types and range type
instantiatePatternType pos con_ty arg_vals ex_vars
  | length (dataConPatternParams con_ty) /= length arg_vals =
      internalError $ "instantiatePatternType: Wrong number of type parameters at " ++ show pos
  | length (dataConPatternExTypes con_ty) /= length ex_vars =
      internalError $ "instantiatePatternType: Wrong number of existential variables at " ++ show pos
  | otherwise = do
      -- Check argument types
      zipWithM_ check_argument_type (dataConPatternParams con_ty) arg_vals
      
      -- Check existential types
      zipWithM_ check_ex_pattern (dataConPatternExTypes con_ty) ex_vars

      -- Instantiate the type
      instantiateDataConType con_ty (map fst arg_vals) (map fst ex_vars)
  where
    check_argument_type (_ ::: expected_type) (_, given_type) =
      checkType (text "Error in type application") pos expected_type given_type
      
    check_ex_pattern (_ ::: expected_type) (_, given_type) =
      checkType (text "Error in type application") pos expected_type given_type
