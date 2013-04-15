{-| A base class for type errors.
-}

module Type.Error
where

import Control.Exception
import Control.Monad.Trans
import Data.Char
import Data.Dynamic
import Data.Typeable
import Text.PrettyPrint.HughesPJ

import Common.SourcePos
import Type.Type
import Type.Var

class Exception e => TypeError e

-- | Type errors are a subclass of 'Exception'
data SomeTypeError where
  SomeTypeError :: TypeError e => e -> SomeTypeError
  deriving(Typeable)

instance Show SomeTypeError where show (SomeTypeError e) = show e

instance Exception SomeTypeError

typeErrorToSomeException :: TypeError e => e -> SomeException
typeErrorToSomeException = toException . SomeTypeError

typeErrorFromSomeException :: TypeError e => SomeException -> Maybe e
typeErrorFromSomeException e = do 
  SomeTypeError te <- fromException e
  cast te

throwTypeError :: (TypeError e, MonadIO m) => e -> m a
throwTypeError = liftIO . throwIO

-------------------------------------------------------------------------------
-- Text processing

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
showOrdinal n
  | abs ((n `div` 10) `rem` 10) == 1 = th -- 11th .. 19th
  | abs (n `rem` 10) == 1            = st -- 21st, 31st, ...
  | abs (n `rem` 10) == 2            = nd -- 22nd, 32nd, ...
  | abs (n `rem` 10) == 3            = rd -- 23rd, 33rd, ...
  | otherwise                        = th
  where
    th = show n ++ "th"
    nd = show n ++ "nd"
    rd = show n ++ "rd"
    st = show n ++ "st"

levelString :: Level -> String
levelString SortLevel = "sort"
levelString KindLevel = "kind"
levelString TypeLevel = "type"
levelString ObjectLevel = "value"

-- | Capitalize the first letter of a word or phrase
capitalize :: String -> String
capitalize [] = []
capitalize (c:cs) = toUpper c : cs

-------------------------------------------------------------------------------
-- Type errors

-- | Information about a type checking error, for display to users.
data TypeCheckError =
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
    -- | Type is uninhabited
  | UninhabitedError
    { errorPos        :: SourcePos
    , errorLevel      :: !Level    -- ^ Level (type or kind) of uninhabited thing
    , actualType      :: Type
    }
    deriving(Typeable)

instance TypeError TypeCheckError

instance Exception TypeCheckError where
  toException = typeErrorToSomeException
  fromException = typeErrorFromSomeException

genericTypeMismatch :: SourcePos -> Level -> Type -> Type -> TypeCheckError
genericTypeMismatch pos lv expected actual =
  TypeMismatch pos lv (text "unspecified location") expected actual

typeArgKindMismatch :: SourcePos -> Int -> Type -> Type -> TypeCheckError
typeArgKindMismatch pos index expected actual = let
  ord = text $ showOrdinal index ++ " type argument of a type application"
  in TypeMismatch pos KindLevel ord expected actual

argTypeMismatch :: SourcePos -> Int -> Type -> Type -> TypeCheckError
argTypeMismatch pos index expected actual = let
  ord = text $ showOrdinal index ++ " argument of an application"
  in TypeMismatch pos TypeLevel ord expected actual

badTypeApplication :: SourcePos -> Type -> Kind -> TypeCheckError
badTypeApplication pos operator_type given =
  BadTyApp pos operator_type given

badApplication :: SourcePos -> Type -> Type -> TypeCheckError
badApplication pos operator_type given =
  BadApp pos operator_type given

tyBinderKindMismatch :: SourcePos -> Var -> Type -> Type -> TypeCheckError
tyBinderKindMismatch pos bound_var expected actual = let
  loc = text "binding of" <+> pprVar bound_var
  in TypeMismatch pos KindLevel loc expected actual

binderTypeMismatch :: SourcePos -> Var -> Type -> Type -> TypeCheckError
binderTypeMismatch pos bound_var expected actual = let
  loc = text "binding of" <+> pprVar bound_var
  in TypeMismatch pos TypeLevel loc expected actual

typeObjTypeMismatch :: SourcePos -> Type -> Type -> TypeCheckError
typeObjTypeMismatch pos expected actual =
  TypeMismatch pos TypeLevel (text "constructor type object") expected actual

missingTypeObj :: SourcePos -> TypeCheckError
missingTypeObj pos = MiscError pos (text "Missing type object")

unwantedTypeObj :: SourcePos -> TypeCheckError
unwantedTypeObj pos = MiscError pos (text "Unexpected type object")

sizeParamTypeMismatch :: SourcePos -> Int -> Type -> Type -> TypeCheckError
sizeParamTypeMismatch pos index expected actual = let
  ord = text $ showOrdinal index ++ " size parameter"
  in TypeMismatch pos TypeLevel ord expected actual

sizeParamLengthMismatch :: SourcePos -> Int -> Int -> TypeCheckError
sizeParamLengthMismatch pos expected actual = let
  message = "Expecting " ++ show expected ++ "size parameters, got " ++
            show actual
  in MiscError pos (text message)

conFieldTypeMismatch :: SourcePos -> Int -> Type -> Type -> TypeCheckError
conFieldTypeMismatch pos index expected actual = let
  ord = text $ showOrdinal index ++ " constructor field"
  in TypeMismatch pos TypeLevel ord expected actual

conFieldLengthMismatch :: SourcePos -> Int -> Int -> TypeCheckError
conFieldLengthMismatch pos expected actual = let
  message = "Expecting " ++ show expected ++ "constructor arguments, got " ++
            show actual
  in MiscError pos (text message)

badUnboxedTupleField :: SourcePos -> Int -> Type -> TypeCheckError
badUnboxedTupleField pos index actual = let
  ord = text $ showOrdinal index ++ " unboxed tuple field"
  in PolyTypeMismatch pos KindLevel ord [valT, boxT] actual

returnTypeMismatch :: SourcePos -> Type -> Type -> TypeCheckError
returnTypeMismatch pos expected actual =
  TypeMismatch pos TypeLevel (text "return type") expected actual

emptyCaseError :: SourcePos -> TypeCheckError
emptyCaseError pos =
  MiscError pos (text "Empty case expression")

inconsistentCaseAlternatives :: SourcePos -> Int -> Type -> Type -> TypeCheckError
inconsistentCaseAlternatives pos index first_type this_type = let
  ord = text $ showOrdinal index ++ " case alternative"
  in TypeMismatch pos TypeLevel ord first_type this_type

scrutineeTypeMismatch :: SourcePos -> Type -> Type -> TypeCheckError
scrutineeTypeMismatch pos expected actual =
  TypeMismatch pos TypeLevel (text "scrutinee of case expression")
  expected actual

typeVariableEscapes :: SourcePos -> Var -> TypeCheckError
typeVariableEscapes = EscapeError

wrongPatternBinderCount :: SourcePos -> Int -> Int -> TypeCheckError
wrongPatternBinderCount pos expected_count actual_count = 
  MiscError pos (text "Pattern should have" <+> int expected_count <+>
                 text "fields, but it has" <+> int actual_count)

coercionTypeMismatch :: SourcePos -> Type -> Type -> TypeCheckError
coercionTypeMismatch pos expected actual =
  TypeMismatch pos TypeLevel (text "argument of coercion expression")
  expected actual

arrayConTypeMismatch :: SourcePos -> Int -> Type -> Type -> TypeCheckError
arrayConTypeMismatch pos index expected actual = let
  ord = text $ showOrdinal index ++ " element of array"
  in TypeMismatch pos TypeLevel ord expected actual

constantTypeMismatch :: SourcePos -> Type -> Type -> TypeCheckError
constantTypeMismatch pos expected actual =
  TypeMismatch pos TypeLevel (text "constant") expected actual

instance Show TypeCheckError where
  show err =
    show $
    case err
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
       UninhabitedError pos lv ty ->
         formatUninhabitedTypeError pos lv (pprType ty)

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

formatUninhabitedTypeError pos loc ty = let
  intro = text "Error at" <+> text (show pos)
  in intro $$ text "Kind" <+> ty <+> text "is uninhabited"