
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
import Type.Error
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
type TCM b a = TypeEvalM b a

lookupVar :: BoxingMode b => Var -> TCM b Type
lookupVar v = do
  m_ty <- lookupType v
  case m_ty of
    Just rt -> return rt
    Nothing -> internalError $ "lookupVar: No type for variable: " ++ show v

tcLookupDataCon :: BoxingMode b => Var -> TCM b DataConType
tcLookupDataCon v = do
  m_dct <- lookupDataCon v
  case m_dct of
    Just dct -> return dct
    Nothing -> internalError $ "lookupVar: No type for data constructor: " ++ show v

-- | Throw an error if the given types do not match
checkType :: BoxingMode b =>
             (Type -> Type -> TypeCheckError) -> Type -> Type -> TCM b ()
checkType make_message expected given = do
  ok <- compareTypes expected given 
  unless ok $ throwTypeError $ make_message expected given

checkLiteralType :: Lit -> TCM b ()
checkLiteralType l =
  if isValidLiteralType (literalType l) l
  then return ()
  else error "Not a valid literal type"
  where
    isValidLiteralType ty lit =
      -- Get the type constructor
      case fromVarApp ty
      of Just (v, args) ->
           -- Based on the literal, check whether the type constructor is 
           -- acceptable
           case lit
           of IntL _ _ -> v == intV
              FloatL _ _ -> v == floatV
         Nothing ->
           -- Literals cannot have other types 
           False

-- | Instantiate a data constructor's type in a pattern, given the
--   pattern's type arguments.
--   Verify that the argument type kinds and existental type kinds are correct.
instantiatePatternType :: BoxingMode b =>
                          SourcePos -- ^ Position where pattern was mentioned
                       -> DataConType    -- ^ Constructor to instantiate
                       -> [(Type, Type)] -- ^ Each type argument and its kind
                       -> [(Var, Type)]  -- ^ Each existential variable and its kind
                       -> TCM b ([Binder], [Type], Type)
                       -- ^ Compute field types and range type
instantiatePatternType pos con_ty arg_vals ex_vars
  | length (dataConTyParams con_ty) /= length arg_vals =
      internalError $ "instantiatePatternType: Wrong number of type parameters at " ++ show pos
  | length (dataConExTypes con_ty) /= length ex_vars =
      internalError $ "instantiatePatternType: Wrong number of existential variables at " ++ show pos
  | otherwise = do
      -- Check argument types
      mapM_ check_argument_type $ zip3 [1..] (dataConTyParams con_ty) arg_vals
      
      -- Check existential types
      mapM_ check_ex_pattern $ zip3 [1..] (dataConExTypes con_ty) ex_vars

      -- Instantiate the type
      instantiateDataConType con_ty (map fst arg_vals) (map fst ex_vars)
  where
    check_argument_type (index, _ ::: expected_type, (arg, given_type)) = do
      checkType (typeArgKindMismatch pos index) expected_type given_type
      
    check_ex_pattern (_, _ ::: expected_type, (var, given_type)) = do
      checkType (tyBinderKindMismatch pos var) expected_type given_type

