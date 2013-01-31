
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
-- Type errors

-- | Print a number as an English ordinal
showOrdinal :: Int -> String
showOrdinal 0 = "zeroth"
showOrdinal 1 = "first"
showOrdinal 2 = "second"
showOrdinal 3 = "third"
showOrdinal 4 = "fourth"
showOrdinal 5 = "fifth"
showOrdinal 6 = "sixth"
showOrdinal 7 = "seventh"
showOrdinal 8 = "eighth"
showOrdinal 9 = "ninth"
showOrdinal 10 = "tenth"
showOrdinal n =
  case abs $ n `rem` 10
  of 1 -> show n ++ "st"
     2 -> show n ++ "nd"
     3 -> show n ++ "rd"
     _ -> show n ++ "th"

-- | Information about a type error is collected in this data structure
--   so that it can be formatted nicely for users.
--
--   Erroneous expressions are represented in 'Doc' format so that this
--   data structure is independent of the expression data type.
data TypeError =
    -- | Kind mismatch or type mismatch
    TypeMismatch
    { errorPos        :: SourcePos
    , errorLevel      :: !Level    -- ^ Level (type or kind) where error found
    , errorLocation   :: Doc       -- ^ Description of where error occurred
    , expectedKind    :: Type      -- ^ Expected type or kind
    , actualKind      :: Type      -- ^ Actual type or kind
    }
    -- | Kind mismatch in a polykinded location
  | PolyTypeMismatch
    { errorPos        :: SourcePos
    , errorLevel      :: !Level    -- ^ Level (type or kind) where error found
    , errorLocation   :: Doc       -- ^ Description of where error occurred
    , expectedKinds   :: [Type]    -- ^ Expected type or kind
    , actualKind      :: Type      -- ^ Actual type or kind
    }    
    -- | Applied a non-function to a type argument
  | BadTyApp
    { errorPos        :: SourcePos
    , operatorType    :: Type
    , argumentKind    :: Kind
    }
    -- | Applied a non-function to a type argument
  | BadApp
    { errorPos        :: SourcePos
    , operatorType    :: Type
    , argumentType    :: Type
    }
    -- | A type variable escapes its scope
  | EscapeError
    { errorPos        :: SourcePos
    , errorVar        :: Var
    }
    -- | Miscellaneous error with no detailed information
  | MiscError
    { errorPos        :: SourcePos
    , errorMessage    :: Doc
    }

genericTypeMismatch :: SourcePos -> Level -> Type -> Type -> TypeError
genericTypeMismatch pos lv expected actual =
  TypeMismatch pos lv (text "unspecified location") expected actual

typeArgKindMismatch :: SourcePos -> Int -> Type -> Type -> TypeError
typeArgKindMismatch pos index expected actual = let
  ord = text $ showOrdinal index ++ " type argument of a type application"
  in TypeMismatch pos KindLevel ord expected actual

argTypeMismatch :: SourcePos -> Int -> Type -> Type -> TypeError
argTypeMismatch pos index expected actual = let
  ord = text $ showOrdinal index ++ " argument of an application"
  in TypeMismatch pos TypeLevel ord expected actual

tyBinderKindMismatch :: SourcePos -> Var -> Type -> Type -> TypeError
tyBinderKindMismatch pos bound_var expected actual = let
  loc = text "binding of" <+> pprVar bound_var
  in TypeMismatch pos KindLevel loc expected actual

binderTypeMismatch :: SourcePos -> Var -> Type -> Type -> TypeError
binderTypeMismatch pos bound_var expected actual = let
  loc = text "binding of" <+> pprVar bound_var
  in TypeMismatch pos TypeLevel loc expected actual

conFieldTypeMismatch :: SourcePos -> Int -> Type -> Type -> TypeError
conFieldTypeMismatch pos index expected actual = let
  ord = text $ showOrdinal index ++ " constructor field"
  in TypeMismatch pos TypeLevel ord expected actual

conFieldLengthMismatch :: SourcePos -> Int -> Int -> TypeError
conFieldLengthMismatch pos expected actual = let
  message = "Expecting " ++ show expected ++ "constructor arguments, got " ++
            show actual
  in MiscError pos (text message)

badUnboxedTupleField :: SourcePos -> Int -> Type -> TypeError
badUnboxedTupleField pos index actual = let
  ord = text $ showOrdinal index ++ " unboxed tuple field"
  in PolyTypeMismatch pos KindLevel ord [valT, boxT] actual

returnTypeMismatch :: SourcePos -> Type -> Type -> TypeError
returnTypeMismatch pos expected actual =
  TypeMismatch pos TypeLevel (text "return type") expected actual

emptyCaseError :: SourcePos -> TypeError
emptyCaseError pos =
  MiscError pos (text "Empty case expression")

inconsistentCaseAlternatives :: SourcePos -> Int -> Type -> Type -> TypeError
inconsistentCaseAlternatives pos index first_type this_type = let
  ord = text $ showOrdinal index ++ " case alternative"
  in TypeMismatch pos TypeLevel ord first_type this_type

scrutineeTypeMismatch :: SourcePos -> Type -> Type -> TypeError
scrutineeTypeMismatch pos expected actual =
  TypeMismatch pos TypeLevel (text "scrutinee of case expression")
  expected actual

typeVariableEscapes :: SourcePos -> Var -> TypeError
typeVariableEscapes = EscapeError

wrongPatternBinderCount :: SourcePos -> Int -> Int -> TypeError
wrongPatternBinderCount pos expected_count actual_count = 
  MiscError pos (text "Pattern should have" <+> int expected_count <+>
                 text "fields, but it has" <+> int actual_count)

coercionTypeMismatch :: SourcePos -> Type -> Type -> TypeError
coercionTypeMismatch pos expected actual =
  TypeMismatch pos TypeLevel (text "argument of coercion expression")
  expected actual

arrayConTypeMismatch :: SourcePos -> Int -> Type -> Type -> TypeError
arrayConTypeMismatch pos index expected actual = let
  ord = text $ showOrdinal index ++ " element of array"
  in TypeMismatch pos TypeLevel ord expected actual

constantTypeMismatch :: SourcePos -> Type -> Type -> TypeError
constantTypeMismatch pos expected actual =
  TypeMismatch pos TypeLevel (text "constant") expected actual

typeError :: TypeError -> m a
typeError err = error $ show doc 
  where
    doc = case err
          of TypeMismatch pos level loc expected actual ->
               formatMismatchError pos level loc
               (pprType expected) (pprType actual)
             PolyTypeMismatch pos level loc expected actual ->
               formatMismatchError pos level loc
               (fsep $ punctuate comma $ map pprType expected) (pprType actual)
             BadTyApp pos ty k ->
               formatBadAppError True pos ty k
             BadApp pos ty t ->
               formatBadAppError False pos ty t
             MiscError pos message ->
               formatMiscError pos message

-- | Create the string form of a 'TyArgMismatch' or 'ArgMismatch'
formatMismatchError :: SourcePos -> Level -> Doc -> Doc -> Doc -> Doc
formatMismatchError pos level location expected actual = let
  level_doc    = case level
                 of TypeLevel -> text "Type"
                    KindLevel -> text "Kind"
  pos_doc      = text $ show pos
  intro        = sep [level_doc <+> text "mismatch in" <+> location,
                      text "at" <+> pos_doc]
  expected_doc = hang (text "Expected") 9 expected
  actual_doc   = hang (text "Got") 9 actual
  in intro $$ expected_doc $$ actual_doc

formatBadAppError :: Bool -> SourcePos -> Type -> Type -> Doc
formatBadAppError is_type_arg pos actual arg_type = let
  err_msg = if is_type_arg
            then text "but it does not take a type argument"
            else text "but it does not take an argument"
  intro = text "Error at" <+> text (show pos)
  oper  = text "Operator of type" <+> pprType actual
  arg   = let description =
                if is_type_arg
                then text "is applied to a type argument of kind"
                else text "is applied to an argument of type"
          in description <+> pprType arg_type <> comma
  in intro $$ oper $$ arg $$ err_msg

formatMiscError pos message =
  text "Error at" <+> text (show pos) $$ message

-------------------------------------------------------------------------------
-- Type-checking environment

-- | The type-checking monad
type TCM a = TypeEvalM a

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
checkType :: (Type -> Type -> TypeError) -> Type -> Type -> TCM ()
checkType make_message expected given = do
  ok <- compareTypes expected given 
  unless ok $ typeError $ make_message expected given

checkLiteralType :: Lit -> TCM ()
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
instantiatePatternType :: SourcePos -- ^ Position where pattern was mentioned
                       -> DataConType    -- ^ Constructor to instantiate
                       -> [(Type, Type)] -- ^ Each type argument and its kind
                       -> [(Var, Type)]  -- ^ Each existential variable and its kind
                       -> TCM ([Binder], [Type], Type)
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

