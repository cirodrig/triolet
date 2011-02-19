{-| Type inference and name resolution for low-level source code.

The responsibilities of this module are to resolve names and infer data types.
There are two kinds of names: variable names and type names.
The currently visible names are stored in an 'Env' value and found by
'lookupEntity'.  The environment also stores type information.  After inferring
data types, record type definitions are no longer needed, so they're excluded
from the output.

Inter-module name resolution is accomplished with the help of explicit
importing and exporting of external symbols.  As in C, declarations of 
external symbols are assumed to be correct without verifying that the
external definition matches the local declaration.   Definitions of externally
visible symbols whose names match the builtins in "LowLevel.Builtins" are
changed to reference the corresponding built-in variable.  Only externally
visible symbols are changed to reference builtins.

Type inference is local.  That is, the type of any expression can be
inferred given the expression itself and the type environment.
-}

{-# LANGUAGE TypeFamilies, FlexibleInstances, ScopedTypeVariables,
  DoRec, Rank2Types, EmptyDataDecls, StandaloneDeriving,
  TypeSynonymInstances #-}
module LLParser.TypeInference
       (Typed, TExp(..), NamedType(..), TypedRecord(..), TypeSynonym(..),
        typedRecordFields,
        applyTemplate,
        dereferenceTypeSynonym,
        exprType, atomType, stmtType,
        convertToValueType,
        convertToStaticFieldType,
        convertToStaticRecord,
        typeInferModule)
where

import Prelude hiding(mapM)

import Control.Applicative
import Control.Monad hiding(mapM)
import Control.Monad.Fix
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Traversable
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import Common.Label
import LLParser.AST
import LowLevel.Build
import LowLevel.Builtins
import LowLevel.FreshVar
import LowLevel.CodeTypes hiding(Field, fieldType, recordFields)
import qualified LowLevel.Print as LL
import qualified LowLevel.Syntax as LL
import Globals

data Typed

type instance Expr Typed = TExp
type instance VarName Typed = LL.Var
type instance RecordName Typed = NamedType

-- | A type-annotated expression
data TExp = TExp {expType :: [Type Typed], expExp :: !(BaseExpr Typed)}


-- Show instances, for debugging.

deriving instance Show (Type Typed)
deriving instance Show (TypeArg Typed)
deriving instance Show (FieldDef Typed)

instance Show TExp where
  show _ = "TExp"

-- | Record fields are not shown.  Fields tend to cause non-terminating
--   evaluation if we try to show them during type inference, because of
--   how they interace with name lookup.
instance Show TypedRecord where
  show recd = 
    case recd
    of TypedRecord nm xs
         | null xs -> nm
         | otherwise -> 
         nm ++ "(" ++ intercalate "," (replicate (length xs) "_") ++ ")"

instance Show ParametricType where
  show _ = "ParametricType"

-------------------------------------------------------------------------------
-- Type-parameterized things

-- | An applicative interpretation of manyary functions.  We use this to
-- implement parameterized record types.
data Parameterized dom rng =
  Parameterized 
  { arity :: !(Maybe Int)
  , apply :: [dom] -> rng
  }

applyTo :: [dom] -> Parameterized dom rng -> rng
applyTo dom x =
  case arity x
  of Just n | n /= length dom -> internalError "applyTo"
     _ -> apply x dom

-- | Ignore arity and apply to some dummy arguments.
--   Use this to view the contents of
--   the Parameterized object for debugging.
applyToNonces x =
  let dummy_args =
        [NamedT $ RecordT $ TypedRecord ("arg" ++ show n) [] | n <- [1..]]
  in apply x dummy_args

-- | Parameters are de Bruijn indices
newtype TypeParameter = TypeParameter Int

type TypeParametric a = Parameterized (TypeArg Typed) a
type ParametricType = TypeParametric (Type Typed)

pVar n (TypeParameter i) = Parameterized (Just n) (\xs -> xs !! i)

instance Functor (Parameterized dom) where
  fmap f (Parameterized n app) =
    Parameterized n (\dom -> f (app dom))

instance Applicative (Parameterized dom) where
  pure x = Parameterized Nothing (\_ -> x)
  f <*> x = Parameterized n $ \env ->
    let f' = apply f env
        x' = apply x env
    in f' x'
    where
      n = case arity f
          of Nothing -> arity x
             Just n1 ->
               case arity x
               of Nothing -> Just n1
                  Just n2 | n1 == n2 -> Just n2
                          | otherwise -> internalError "Parameterized.(<*>)"

-------------------------------------------------------------------------------

fromTypeArg (TypeArg t) = t
fromTypeArg (ExprArg _) = error "Expression argument found where type expected"

fromExprArg (ExprArg e) = e
fromExprArg (TypeArg _) = error "Type argument found where expression expected"

data NamedType =
    RecordT !TypedRecord
  | TemplateT ParametricType
  | SynonymT !TypeSynonym
    deriving(Show)

isTypeSynonym (SynonymT {}) = True
isTypeSynonym _ = False

-- | If the given type is a type synonym, get its actual value.
--   Otherwise, return the type.  The return value is never a type synonym.
dereferenceTypeSynonym :: Type Typed -> Type Typed
dereferenceTypeSynonym (NamedT (SynonymT syn)) = typeSynonymValue syn
dereferenceTypeSynonym t = t

data TypeSynonym =
    TypeSynonym
    { -- | The type synonym's ID.  Type synonyms with the same ID represent
      --   the same type.  When creating LowLevel code, record layouts are 
      --   computed, then looked up when the type synonym is used.
      typeSynonymID :: !(Ident TypedRecord)
    , typeSynonymValue :: Type Typed
    }
    deriving(Show)

-- | A record type.
data TypedRecord =
    TypedRecord
    { -- | The record name given in source code.  This is only used for
      --   error messages.
      typedRecordName :: String
      -- | The record's fields.  If the record is parametric, the fields will 
      --   require type parameters to compute.  The fields take the 
      --   parameters of the record.
    , typedRecordFields :: [FieldDef Typed]
    }

applyTemplate :: Type Typed -> [TypeArg Typed] -> Type Typed
applyTemplate (NamedT (TemplateT tmpl)) args = apply tmpl args

-- | A named entity
data DictEntry =
    -- | A variable
    VarEntry (Type Typed) !LL.Var
    -- | A type definition
  | TypeEntry (Type Typed)
    -- | A type parameter.
  | TypeParameterEntry TypeParameter

-- | A dictionary associates each source code name with a variable or record
-- type.
type Dict = Map.Map String DictEntry

emptyDict = Map.empty

-- | Code has multiple nested scopes
data Scope =
    RecScope
    { completeDict :: Dict        -- ^ Fully built dictionary
    , partialDict :: !Dict        -- ^ Partially built dictionary
    }
  | NonRecScope !Dict

-- | The name resolution monad.
newtype NR a = NR {runNR :: NREnv -> Env -> Errors -> IO (a, Env, Errors)}

-- | Global constant data used by name resolution
data NREnv =
  NREnv
  { -- | Variable IDs
    varIDSupply :: {-# UNPACK #-}!(Supply (Ident LL.Var))
    -- | Type synonym IDs
  , synonymIDSupply :: {-# UNPACK #-}!(Supply (Ident TypedRecord))
    -- | Externally defined or externally visible global variables
  , externalVariables :: ![LL.Var]
    -- | Name of the source module.  Used to create variable names.
  , sourceModuleName  :: !ModuleName
  }

data Env = Env { nextTypeParameter :: {-# UNPACK #-}!Int
               , currentScope :: [Scope]
               }

type Errors = [String] -> [String]

instance Functor NR where
  fmap f m = NR $ \ctx env errs -> do
    (x, env', errs') <- runNR m ctx env errs
    return (f x, env', errs')

instance Applicative NR where
  {-# INLINE (<*>) #-}
  pure = return
  t <*> x = do f <- t
               fmap f x

instance Monad NR where
  {-# INLINE return #-}
  {-# INLINE (>>=) #-}
  return x = NR (\_ env errs -> return (x, env, errs))
  m >>= k = NR $ \ctx env errs -> do
    (x, env', errs') <- runNR m ctx env errs
    runNR (k x) ctx env' errs'

instance MonadFix NR where
  mfix f = NR $ \ctx env errs -> do
    rec rv@(x, env', errs') <- runNR (f x) ctx env errs
    return rv

instance Supplies NR (Ident LL.Var) where
  fresh = NR $ \ctx env errs -> do
    x <- supplyValue (varIDSupply ctx)
    return (x, env, errs)

instance Supplies NR (Ident TypedRecord) where
  fresh = NR $ \ctx env errs -> do
    x <- supplyValue (synonymIDSupply ctx)
    return (x, env, errs)

getSourceModuleName :: NR ModuleName 
getSourceModuleName = NR $ \env ctx errs ->
  return (sourceModuleName env, ctx, errs)

getExternalVars :: NR [LL.Var]
getExternalVars = NR $ \env ctx errs ->
  return (externalVariables env, ctx, errs)

addError :: String -> Errors -> Errors
addError err errs = (err :) . errs

addErrorMaybe :: Maybe String -> Errors -> Errors
addErrorMaybe err errs = maybe id (:) err . errs

-- | If the argument is a 'Just' value, report the string as an error.
-- The argument is used lazily.
throwErrorMaybe :: Maybe String -> NR ()
throwErrorMaybe err = NR $ \_ env errs -> 
  return ((), env, addErrorMaybe err errs)

-- | Enter a recursive scope.  Start building a local dictionary; pass the
-- final dictionary back in as input when done.
enterRec :: NR a -> NR a
enterRec m = NR $ \ctx env errs -> do
  rec { let init_local_scope =
             RecScope { completeDict = partialDict (head $ currentScope env')
                      , partialDict = emptyDict
                      }
            init_env = env {currentScope = init_local_scope : currentScope env}
        ; (x, env', errs') <- runNR m ctx init_env errs
        ; let env'' = Env { nextTypeParameter = nextTypeParameter env
                          , currentScope = tail $ currentScope env'} }
  return (x, env'', errs')

-- | Enter a nonrecursvie scope.
enterNonRec :: NR a -> NR a
enterNonRec m = NR $ \ctx env errs -> do
  let local_env = env {currentScope = NonRecScope emptyDict : currentScope env}
  (x, env', errs') <- runNR m ctx local_env errs
  let env'' = Env { nextTypeParameter = nextTypeParameter env
                  , currentScope = tail $ currentScope env'}
  return (x, env'', errs')

-- | Add a definition to the current scope.  If the definition conflicts
-- with an existing definition, an error is reported.
defineEntity :: String -> DictEntry -> NR ()
defineEntity name value = NR $ \ctx env errs ->
  case currentScope env
  of scope : scopes ->
       case scope
       of RecScope {partialDict = pd}
            | name `Map.member` pd ->
                -- The same name was defined repeatedly in a recursive
                -- scope.  Report an error.
                let error_message = "Name '" ++ name ++ "' is redefined"
                in return ((), env, addError error_message errs)
            | otherwise ->
                -- Add the definition to the partial dictionary.
                let scope' = scope {partialDict = Map.insert name value $
                                                  partialDict scope}
                    env' = env {currentScope = scope' : scopes}
                in return ((), env', errs)
          NonRecScope d -> 
            -- Add the definition to the non-recursive dictionary.
            let scope' = NonRecScope (Map.insert name value d)
                env' = env {currentScope = scope' : scopes}
            in return ((), env', errs)

-- | Look up a name.  If the name is not found, then an error is reported, 
-- the returned entry is undefined, and False is returned.  The returned
-- entry and boolean value should be used lazily.
lookupEntity :: String -> NR (DictEntry, Bool)
lookupEntity name = NR $ \_ env errs ->
  -- Ensure that the returned values are non-strict
  let (entry, is_defined, err) = lookup_name $ currentScope env
  in return ((entry, is_defined), env, addErrorMaybe err errs)
  where
    lookup_name (scope : scopes) =
      let dict =
            case scope
            of RecScope {completeDict = cd} -> cd
               NonRecScope d -> d
      in case Map.lookup name dict
         of Just e  -> (e, True, Nothing)
            Nothing -> lookup_name scopes
    
    -- If the entire environment has been searched, then fail
    lookup_name [] = (internalError ("lookupEntity: not found: " ++ name),
                      False,
                      Just $ "Undefined name: '" ++ name ++ "'")

-- | Create a new type synonym and add it to the environment.
createTypeSynonym :: TypeName Parsed -> Type Typed -> NR (RecordName Typed)
createTypeSynonym name value = do
  type_id <- fresh
  let synonym = TypeSynonym type_id value
  defineEntity name (TypeEntry $ NamedT $ SynonymT synonym)
  return $ SynonymT synonym

defineTypeParam :: TypeName Parsed -> NR ()
defineTypeParam name = NR $ \ctx env errs ->
  let index = nextTypeParameter env
      env' = env {nextTypeParameter = index + 1}
      define_type_param =
        defineEntity name (TypeParameterEntry (TypeParameter index))
  in runNR define_type_param ctx env' errs

-- | Get the number of type parameters that are free at the current
--   point.
getCurrentTypeArity :: NR Int
getCurrentTypeArity = NR $ \ctx env errs ->
  let arity = nextTypeParameter env
  in return (arity, env, errs)

-- | Create a new variable.  The definition is not added to the environment.
--
-- A module name may optionally be specified; if not given, it defaults to the
-- current input file's module.
createVar :: String -> ValueType -> NR LL.Var
createVar name ty = do
  module_name <- getSourceModuleName
  let label = pyonLabel module_name name
  LL.newVar (Just label) ty

{-
-- | Create an externally visible variable.  The definition is not added to
-- the environment.
createExternalVar :: ModuleName -> String -> Maybe String -> ValueType
                  -> NR LL.Var
createExternalVar module_name name ext_name ty = do
  let label = pyonLabel module_name name
  LL.newExternalVar label ty-}

-- | Create a global variable in the current module.  If the variable has
-- already been declared, return the declared variable instead of creating
-- something.
createGlobalVar :: VarName Parsed -> ValueType -> NR LL.Var
createGlobalVar name ty = do
  -- Was this variable name declared to be external?
  external_vars <- getExternalVars
  case find is_name external_vars
    of Nothing ->
         -- Not external; create a new variable
         createVar name ty
       Just evar 
         | ty /= LL.varType evar ->
             error $ "Type of external declaration does not match " ++
                     "type of variable definition"
         | otherwise -> return evar -- Return the already created variable
  where
    -- Check if variable's unqualified name matches given name
    is_name v =
      case LL.varName v
      of Just nm -> name == labelLocalNameAsString nm
         Nothing -> False

-- | Add a variable definition to the environment
defineVar :: LL.Var -> Type Typed -> NR ()
defineVar v t =
  let name = case LL.varName v
             of Just lab -> labelLocalNameAsString lab 
                Nothing -> internalError "defineVar"
  in defineEntity name (VarEntry t v)

-- | Process a definition of a name, creating a new variable.
createAndDefineVar :: String -> Type Typed -> NR LL.Var
createAndDefineVar name ty = do
  v <- createVar name (convertToValueType ty)
  defineVar v ty
  return v

lookupVar :: String -> NR (TypeParametric (Expr Typed))
lookupVar name = do
  (entry, is_defined) <- lookupEntity name
  type_arity <- getCurrentTypeArity
  throwErrorMaybe $
    if is_defined
    then case entry
         of VarEntry _ _ -> Nothing
            TypeParameterEntry _ -> Nothing
            _ -> Just $ "Not a variable: '" ++ name ++ "'"
    else Just $ "Not defined: '" ++ name ++ "'"
  return (var_expr type_arity entry)
  where
    var_expr _          (VarEntry t v) = pure (TExp [t] (VarE v))
    var_expr type_arity (TypeParameterEntry tp) =
      fmap fromExprArg $ pVar type_arity tp

-- | Define a new record type
defineRecord :: RecordName Parsed
             -> Int
             -> [TypeParametric (FieldDef Typed)]
             -> NR ()
defineRecord name nparams mk_fields = do
  defineEntity name (TypeEntry record)
  where
    record =
      if nparams == 0
      then instantiate_record []
      else NamedT $ TemplateT create_parametric_record
    
    create_parametric_record = Parameterized (Just nparams) instantiate_record

    instantiate_record tmpl_params =
      NamedT $ RecordT $ TypedRecord name (map (applyTo tmpl_params) mk_fields)

-------------------------------------------------------------------------------

check :: Maybe String -> a -> a
check Nothing x        = x
check (Just message) _ = error message

-- | Report an error if the expected type does not match the given type. 
expectType :: PrimType          -- ^ Expected type
           -> String            -- ^ Error message
           -> [Type Typed]      -- ^ Given type
           -> Maybe String
expectType expected message actual =
  case actual
  of [PrimT pt] | expected == pt -> Nothing
     _ -> Just message

expectNativeWord = expectType nativeWordType

-- | Report an error if the given type is not a \'pointer\' or \'owned\' type.
expectReferenceType :: String            -- ^ Error message
                    -> [Type Typed]      -- ^ Given type
                    -> Maybe String
expectReferenceType message actual =
  case actual
  of [PrimT PointerType] -> Nothing
     [PrimT OwnedType]   -> Nothing
     _ -> Just message

expectRecordType message ty = throwErrorMaybe $
  case ty
  of NamedT (RecordT (TypedRecord {})) -> Nothing
     _ -> Just message

convertToStaticRecord :: TypedRecord -> StaticRecord
convertToStaticRecord recd =
  let field_types = [(m, convertToStaticFieldType t)
                    | FieldDef m t _ <- typedRecordFields recd]
  in staticRecord field_types

convertToValueType :: Type Typed -> ValueType
convertToValueType ty = 
  case dereferenceTypeSynonym ty
  of PrimT pt -> PrimType pt
     NamedT (RecordT record) -> RecordType $ convertToStaticRecord record
     _ -> error "Expecting a value type"

convertToStaticFieldType :: Type Typed -> StaticFieldType
convertToStaticFieldType ty = 
  case dereferenceTypeSynonym ty
  of PrimT pt -> PrimField pt
     NamedT (RecordT record) -> RecordField $ convertToStaticRecord record
     BytesT size align ->
       let size' = convertToIntConstant size
           align' = convertToIntConstant align
       in BytesField size' align'
     ArrayT {} -> error "Record cannot contain an array"
     AppT ty args ->
       -- Apply, then convert
       convertToStaticFieldType $ applyTemplate ty args

convertToIntConstant :: Expr Typed -> Int
convertToIntConstant expr =
  case expExp expr
  of IntLitE ty n -> fromIntegral n
     _ -> internalError "convertToIntConstant: Not an integer constant"

-------------------------------------------------------------------------------
-- Name resolution and inference of types

resolveTypeName :: RecordName Parsed -> NR ParametricType
resolveTypeName nm = do 
  (entry, is_defined) <- lookupEntity nm
  type_arity <- getCurrentTypeArity
  throwErrorMaybe $
    if is_defined
    then case entry
         of VarEntry {} -> Just $ "Not a type: '" ++ nm ++ "'"
            TypeEntry {} -> Nothing
            TypeParameterEntry {} -> Nothing
    else Just $ "Not defined: '" ++ nm ++ "'"
  return $ case entry
           of TypeEntry t -> pure t
              TypeParameterEntry tp -> fmap fromTypeArg $ pVar type_arity tp

resolveTypeName0 :: RecordName Parsed -> NR (Type Typed)
resolveTypeName0 nm = fmap (applyTo []) $ resolveTypeName nm

resolveType :: Type Parsed -> NR ParametricType
resolveType ty =
  case ty
  of PrimT pt -> return (pure (PrimT pt))
     NamedT nm -> resolveTypeName nm
     BytesT size align -> do
       size_expr <- resolveExpr size
       align_expr <- resolveExpr align
       let mktype sz al =
             check (expectNativeWord "Size of type must be a native word" (expType sz)) $
             check (expectNativeWord "Alignment of type must be a native word" (expType al)) $
             BytesT sz al
       return (liftA2 mktype size_expr align_expr)
     ArrayT mut size elt -> do
       size_expr <- resolveExpr size
       elt_ty <- resolveType elt
       let mktype sz elt =
             check (expectNativeWord "Size of array must be a native word" (expType sz)) $
             ArrayT mut sz elt
       return (liftA2 mktype size_expr elt_ty)
     AppT t args -> do
       -- Resolve t and args
       param_t <- resolveType t
       arg_ts <- mapM resolveTypeArg args

       -- Apply resolved parameter to resolved arguments
       return (applyTemplate <$> param_t <*> sequenceA arg_ts)

resolveTypeArg (TypeArg t) = liftM (fmap TypeArg) $ resolveType t
resolveTypeArg (ExprArg e) = liftM (fmap ExprArg) $ resolveExpr e


resolveType0 :: Type Parsed -> NR (Type Typed)
resolveType0 t = fmap (applyTo []) $ resolveType t

-- | Determine the type of a binary operation's result.  Throw errors if the
-- operation is ill-typed.
getBinaryType :: BinOp -> [Type Typed] -> [Type Typed] -> Type Typed
getBinaryType op xs@(~[x]) ys@(~[y]) =
  case op
  of MulOp -> arithmetic
     ModOp -> arithmetic
     DivOp -> division
     IntDivOp -> int_division
     AddOp -> arithmetic
     SubOp -> arithmetic
     PointerAddOp -> pointer
     AtomicAddOp -> atomic
     CmpEQOp -> comparison
     CmpNEOp -> comparison
     CmpLTOp -> comparison
     CmpLEOp -> comparison
     CmpGTOp -> comparison
     CmpGEOp -> comparison
     AndOp -> boolean
     OrOp -> boolean
  where
    single_parameter =
      if length xs == 1 && length ys == 1
      then Nothing
      else Just "Operand has multiple return values" 
      
    primtype_check (PrimT _) = Nothing
    primtype_check _ = Just "Expecting a primitive type"
    
    eq_primtype_check (PrimT x) (PrimT y)
      | x == y = Nothing
      | otherwise = Just "Binary operands not equal"
    
    number_check (PrimT (IntType {})) = Nothing
    number_check (PrimT (FloatType {})) = Nothing
    number_check _ = Just "Expecting integral or floating-point type"

    floating_check (PrimT (FloatType {})) = Nothing
    floating_check _ = Just "Expecting floating-point type"

    pointer_check (PrimT PointerType) = Nothing 
    pointer_check (PrimT OwnedType) = Nothing 
    pointer_check _ = Just "Expecting 'pointer' or 'owned' type"
    
    pointer_only_check (PrimT PointerType) = Nothing 
    pointer_only_check _ = Just "Expecting 'pointer' type"

    native_int_check (PrimT t)
      | t == nativeIntType = Nothing
      | otherwise = Just "Expecting a native int type"

    bool_check (PrimT BoolType) = Nothing
    bool_check _ = Just "Expecting bool type"

    retval `checking` checks = foldr check retval checks
    
    arithmetic =
      x `checking` [ single_parameter
                   , number_check x 
                   , number_check y
                   , eq_primtype_check x y]
    
    division =
      x `checking` [ single_parameter
                   , floating_check x 
                   , floating_check y
                   , eq_primtype_check x y]

    int_division =
      PrimT nativeIntType `checking` [ single_parameter
                                     , number_check x 
                                     , number_check y
                                     , eq_primtype_check x y]

    pointer =
      x `checking` [single_parameter, pointer_check x, native_int_check y]

    atomic =
      y `checking` [single_parameter, pointer_only_check x, primtype_check y]
    
    comparison =
      PrimT BoolType `checking` [ single_parameter
                                , primtype_check x
                                , primtype_check y
                                , eq_primtype_check x y]

    boolean =
      PrimT BoolType `checking` [ single_parameter
                                , bool_check x
                                , bool_check y]

-- | Determine the type of a unary operation's result.  Throw errors if the
-- operation is ill-typed.
getUnaryType :: UnaryOp -> TypeParametric [Type Typed] -> ParametricType
getUnaryType op types = gut <$> types
  where
    gut xs@(~[x]) =
      case op of NegateOp -> negate
      where
        single_parameter =
          case xs of [_] -> Nothing
                     _ -> Just "Operand has multiple return values"

        primtype_check (PrimT _) = Nothing
        primtype_check _ = Just "Expecting a primitive type"

        number_check (PrimT (IntType {})) = Nothing
        number_check (PrimT (FloatType {})) = Nothing
        number_check _ = Just "Expecting integral or floating-point type"

        retval `checking` checks =
          -- FIXME: check checks
          retval
        
        negate =
          x `checking` [single_parameter, number_check x]

exprType :: Expr Typed -> [Type Typed]
exprType = expType

atomType :: Atom Typed -> [Type Typed]
atomType (ValA exprs) = concatMap expType exprs

stmtType :: Stmt Typed -> [Type Typed]
stmtType (LetS _ _ s) = stmtType s
stmtType (LetrecS _ s) = stmtType s
stmtType (TypedefS _ _ s) =
  -- FIXME: If the typedef'd name appears in the type, then substitute the
  -- actual type for it.
  trace "Warning: Unhandled case in stmtType" $ stmtType s
stmtType (IfS _ _ s Nothing) = stmtType s
stmtType (IfS _ _ _ (Just (_, s))) = stmtType s
stmtType (WhileS inits _ _ Nothing) = [t | (Parameter t _, _) <- inits]
stmtType (WhileS _ _ _ (Just (_, s))) = stmtType s
stmtType (ReturnS atom) = atomType atom

-------------------------------------------------------------------------------
-- Name resolution and inference of record definitions

resolveExpr0 :: Expr Parsed -> NR (Expr Typed)
resolveExpr0 expr = fmap (applyTo []) $ resolveExpr expr

resolveExpr :: Expr Parsed -> NR (TypeParametric (Expr Typed))
resolveExpr expr =
  case expr
  of VarE vname -> lookupVar vname
     IntLitE ty n -> do
       ty' <- resolveType ty
       return1 ty' (IntLitE <$> ty' <*> pure n)
     FloatLitE ty n -> do
       ty' <- resolveType ty
       return1 ty' (FloatLitE <$> ty' <*> pure n)
     BoolLitE b ->
       return1 (pure $ PrimT BoolType) (pure $ BoolLitE b)
     NilLitE ->
       return1 (pure $ PrimT UnitType) (pure NilLitE)
     NullLitE ->
       return1 (pure $ PrimT PointerType) (pure NullLitE)
     RecordE ty fields -> do
       ty' <- resolveType ty
       fields' <- mapM resolveExpr fields
       let mkexp t fs = TExp [t] (RecordE t fs)
       return $ mkexp <$> ty' <*> sequenceA fields'
     FieldE base fld -> do
       base' <- resolveExpr base
       fld' <- resolveField fld
       let mkexp b f =
             check (expectReferenceType "Base address must have 'pointer' or 'owned' type" (expType b)) $
             FieldE b f
       return1 (pure $ PrimT PointerType) (mkexp <$> base' <*> fld')
     LoadFieldE base fld -> do
       base' <- resolveExpr base
       fld' <- resolveField fld

       -- Determine the type of the loaded field
       let mkexp b f =
             check (expectReferenceType "Base address must have 'pointer' or 'owned' type" (expType b)) $
             let ty = get_field_type f
             in TExp [ty] (LoadFieldE b f)
             where 
               get_field_type (Field base_type fnames Nothing) = 
                 fieldType base_type fnames
               get_field_type (Field _ _ (Just cast_ty)) = cast_ty
       return (mkexp <$> base' <*> fld')
     DerefE {} -> error "Store expression not valid here"
     LoadE ty base -> do
       ty' <- resolveType ty
       base' <- resolveExpr base
       let mkexp t b =
             check (expectReferenceType "Load expression must have 'pointer' or 'owned' type" (expType b)) $
             TExp [t] (LoadE t b)
       return (mkexp <$> ty' <*> base')
     CallE rtypes f args -> do
       rtypes' <- mapM resolveType rtypes
       f' <- resolveExpr f
       args' <- mapM resolveExpr args
       let mkexp rts f xs =
             check (expectType OwnedType "Called function must have 'owned' type" (expType f)) $
             TExp rts (CallE rts f xs)
       return (mkexp <$> sequenceA rtypes' <*> f' <*> sequenceA args')
     PrimCallE rtypes f args -> do
       rtypes' <- mapM resolveType rtypes
       f' <- resolveExpr f
       args' <- mapM resolveExpr args
       let mkexp rts f xs =
             check (expectType PointerType "Called procedure must have 'pointer' type" (expType f)) $
             TExp rts (PrimCallE rts f xs)
       return (mkexp <$> sequenceA rtypes' <*> f' <*> sequenceA args')
     BinaryE op l r -> do
       l' <- resolveExpr l
       r' <- resolveExpr r
       let mkexp l r =
             let rtype = getBinaryType op (expType l) (expType r)
             in TExp [rtype] (BinaryE op l r)
       return (mkexp <$> l' <*> r')
     UnaryE op e -> do
       e' <- resolveExpr e
       let rtype = getUnaryType op (fmap expType e')
       return1 rtype (UnaryE op <$> e')
     CastE e ty -> do
       e' <- resolveExpr e
       ty' <- resolveType ty
       return1 ty' (CastE <$> e' <*> ty')
     SizeofE ty -> do
       ty' <- resolveType ty
       return1 (pure $ PrimT nativeWordType) (SizeofE <$> ty')
     AlignofE ty -> do
       ty' <- resolveType ty
       return1 (pure $ PrimT nativeWordType) (AlignofE <$> ty')
  where
    return1 t e = return (mktexp <$> t <*> e)
      where mktexp t e = TExp [t] e

resolveAtom :: Atom Parsed -> NR (Atom Typed)
resolveAtom (ValA exprs) = fmap ValA $ mapM resolveExpr0 exprs

resolveStmt :: Stmt Parsed -> NR (Stmt Typed)
resolveStmt stmt =
  case stmt
  of LetS lhs rhs body -> do
       rhs' <- resolveAtom rhs
       lhs' <- resolveLValues lhs (atomType rhs')
       body' <- resolveStmt body
       return $ LetS lhs' rhs' body'
     LetrecS fdefs body -> enterRec $ do
       fdefs' <- mapM (resolveFunctionDef False) fdefs
       body' <- enterNonRec $ resolveStmt body
       return $ LetrecS fdefs' body'
     TypedefS tname ty body -> do
       ty' <- resolveType0 ty
       tname' <- createTypeSynonym tname ty'
       body' <- resolveStmt body
       return $ TypedefS tname' ty' body'
     IfS cond if_true if_false mcont -> do
       cond' <- resolveExpr0 cond
       expectBooleanType "condition of 'if' statement" (exprType cond')

       if_true' <- enterNonRec $ resolveStmt if_true
       if_false' <- enterNonRec $ resolveStmt if_false

       -- The true and false branches must have the same return type
       let if_true_type = stmtType if_true'
           if_false_type = stmtType if_false'
       throwErrorMaybe $
         checkTypeLists "branches of 'if' statement" if_true_type if_false_type
       
       mcont' <- traverse (resolve_cont if_false_type) mcont
       return $ IfS cond' if_true' if_false' mcont'
     WhileS inits cond body mcont -> do
       (init_types, inits', cond', body') <- enterNonRec $ do
         -- Process the initializers.  The initial values are processed before
         -- the accumulator variables, then the accumulator variables are
         -- defined.
         init_values <- mapM (resolveExpr0 . snd) inits
         init_params <- mapM (resolveParameter . fst) inits 
         let init_types = [t | Parameter t _ <- init_params]
         
         -- Accumulators and initializers must have matching types
         sequence_
           [throwErrorMaybe $
            checkTypeLists "initializer of 'while' statement" (exprType e) [t]
           | (e, t) <- zip init_values init_types]

         -- Process the condition; must have boolean type
         cond' <- resolveExpr0 cond
         expectBooleanType "condition of 'while' statement" (exprType cond')

         -- Process the body; must have same type as initializers
         body' <- resolveStmt body
         let body_type = stmtType body'
         throwErrorMaybe $
           checkTypeLists "body of 'while' statement" init_types body_type

         return (init_types, zip init_params init_values,cond', body')

       mcont' <- traverse (resolve_cont init_types) mcont
       return $ WhileS inits' cond' body' mcont'
     ReturnS atom -> do
       atom' <- resolveAtom atom
       return $ ReturnS atom'
  where
    resolve_cont if_return_type (lhs, stmt) = do
      lhs' <- resolveLValues lhs if_return_type
      stmt' <- resolveStmt stmt
      return (lhs', stmt')

expectBooleanType message tys = throwErrorMaybe $
  case tys
  of [PrimT BoolType] -> Nothing
     _ -> Just $ "Expecting boolean type in " ++ message

checkTypeLists :: String -> [Type Typed] -> [Type Typed] -> Maybe String
checkTypeLists message tys1 tys2 = check tys1 tys2
  where
    check (ty1:tys1') (ty2:tys2') =
      case (dereferenceTypeSynonym ty1, dereferenceTypeSynonym ty2)
      of (PrimT t1, PrimT t2)
           | t1 == t2 -> check tys1' tys2'
           | otherwise -> mismatch
         (NamedT (RecordT r1), NamedT (RecordT r2))
           | typedRecordName r1 == typedRecordName r2 -> check tys1' tys2'
           | otherwise -> mismatch
         (BytesT {}, _) -> unexpected
         (AppT {}, _) -> unexpected
         (_, BytesT {}) -> unexpected
         (_, AppT {}) -> unexpected
         _ -> mismatch

    check [] [] = Nothing
        
    check _ _ = mismatch    -- Different numbers of return values

    unexpected = internalError "checkTypeLists: Unexpected type"
    mismatch = Just $ "Type mismatch in " ++ message

resolveLValues :: [LValue Parsed] -> [Type Typed] -> NR [LValue Typed]
resolveLValues lvals tys = do
  throwErrorMaybe $
    if length lvals /= length tys
    then Just "Wrong number of binders on left side of assignment"
    else Nothing
  
  -- This must be lazy in the list of types
  (binders, lvals) <- resolve_lvalues lvals tys
  binders                       -- Bind variables
  return lvals                  -- Return new code
  where
    resolve_lvalues (lv:lvs) ~(ty:tys) = do
      (binder, lv') <- resolveLValue lv ty
      (binder2, lvs') <- resolve_lvalues lvs tys
      return (binder >> binder2, lv':lvs')

    resolve_lvalues [] _ = return (return (), [])

-- | Resolve an LValue.  Return the resolved LValue and code to define any
--   bound variables.
--
--   Bound variables are not defined immediately because the entire LValue
--   must be processed before defining anything -- it may refer to old names
--   that will be shadowed by the definitions.
resolveLValue :: LValue Parsed -> (Type Typed) -> NR (NR (), LValue Typed)
resolveLValue lvalue ty =
  case lvalue
  of VarL vname -> do
       v' <- createVar vname (convertToValueType ty)
       return (defineVar v' ty, VarL v')
     StoreL dest -> do
       dest' <- resolveExpr0 dest
       throwErrorMaybe $ expectReferenceType "Store target must have 'owned' or 'pointer' type" (expType dest')
       return (pass, StoreL dest')
     StoreFieldL dest field -> do
       dest' <- resolveExpr0 dest
       field' <- resolveField0 field
       return (pass, StoreFieldL dest' field')
     UnpackL rectype fields -> do
       rectype' <- resolveType0 rectype
       expectRecordType "Record LValue must have record type" rectype'
       let record = case rectype'
                    of NamedT (RecordT record) -> record
                       _ -> internalError "resolveLValue"
       
       -- Unpack individual fields.  This is lazy in the record type.
       let field_types = [t | FieldDef _ t _ <- typedRecordFields record]

       let unpack_fields (fld:flds) ~(fty:ftys) = do
             (binder, fld') <- resolveLValue fld fty
             (binder2, flds') <- unpack_fields flds ftys
             return (binder >> binder2, fld' : flds')
           unpack_fields [] _ = return (pass, [])
       (binders, fields') <- unpack_fields fields field_types
       
       return (binders, UnpackL rectype' fields')
     WildL -> return (pass, WildL)
  where
    pass = return ()

resolveField :: Field Parsed -> NR (TypeParametric (Field Typed))
resolveField (Field recd fnames mtype) = do 
  record' <- resolveType0 recd
  mtype' <- traverse resolveType mtype
  fnames' <- mapM resolveFieldSpec fnames
  return $ Field record' <$> sequenceA fnames' <*> sequenceA mtype'

resolveFieldSpec :: FieldSpec Parsed -> NR (TypeParametric (FieldSpec Typed))
resolveFieldSpec (RecordFS fname) = return (pure $ RecordFS fname)
resolveFieldSpec (ArrayFS e) = liftM (fmap ArrayFS) $ resolveExpr e

resolveField0 :: Field Parsed -> NR (Field Typed)
resolveField0 f = fmap (applyTo []) $ resolveField f

fieldType :: Type Typed -> [FieldSpec Typed] -> Type Typed
fieldType ty flds =
  let real_ty = dereferenceTypeSynonym ty 
  in case flds
     of RecordFS fname : flds ->
          case real_ty
          of NamedT (RecordT recd) ->
               fieldType (record_field_type recd fname) flds
             _ ->
               error $ "Non-record type does not have field '" ++ fname ++ "'"
        ArrayFS _ : flds ->
          case real_ty
          of ArrayT _ _ elt_ty -> fieldType elt_ty flds
             _ -> error "Base of array index expression is not an array"
        [] -> ty
  where
    record_field_type recd fname =
      case find (\(FieldDef _ _ nm) -> nm == fname) $ typedRecordFields recd
      of Just (FieldDef _ t _) -> t
         Nothing -> error $ "Record type does not have field '" ++ fname ++ "'"

-- | Do type inference on a parameter and add the variable to the environment 
resolveParameter :: Parameter Parsed -> NR (Parameter Typed)
resolveParameter (Parameter ty mname) = do
  ty' <- resolveType0 ty 
  v <- case mname
       of Just nm -> createAndDefineVar nm ty'
          Nothing -> LL.newAnonymousVar (convertToValueType ty')
  return (Parameter ty' (Just v))

-- | Do type inference on a local variable and add the variable to the
--   environment.  The variable is always a pointer.
resolveLocal :: Parameter Parsed -> NR (Parameter Typed)
resolveLocal (Parameter ty mname) = do
  ty' <- resolveType0 ty
  v <- case mname
       of Just nm -> createAndDefineVar nm (PrimT PointerType)
          Nothing -> LL.newAnonymousVar (convertToValueType ty')
  return (Parameter ty' (Just v))

resolveFunctionDef :: Bool -> FunctionDef Parsed -> NR (FunctionDef Typed)
resolveFunctionDef is_global fdef = do
  -- Define the function
  let ftype = if functionIsProcedure fdef then PointerType else OwnedType
  fname <-
    if is_global
    then createGlobalVar (functionName fdef) (PrimType ftype)
    else createVar (functionName fdef) (PrimType ftype)
  defineVar fname (PrimT ftype)
  
  enterNonRec $ do
    params <- mapM resolveParameter $ functionParams fdef
    locals <- mapM resolveLocal $ functionLocals fdef
    returns <- mapM resolveType0 $ functionReturns fdef
    body <- resolveStmt $ functionBody fdef
    
    return $ FunctionDef { functionName = fname
                         , functionIsProcedure = functionIsProcedure fdef
                         , functionInlineRequest = functionInlineRequest fdef
                         , functionLocals = locals
                         , functionParams = params
                         , functionReturns = returns
                         , functionBody = body}

resolveDataDef :: DataDef Parsed -> NR (DataDef Typed)
resolveDataDef ddef = do
  -- Define the data
  dname <- createGlobalVar (dataName ddef) (PrimType $ dataType ddef)
  defineVar dname (PrimT $ dataType ddef)
  
  -- Translate the initializer expression
  dexp <- resolveExpr0 $ dataValue ddef
  
  return $ DataDef dname (dataType ddef) dexp

resolveFieldDef :: FieldDef Parsed
                -> NR (TypeParametric (FieldDef Typed))
resolveFieldDef (FieldDef mutability ty name) = do
  ty' <- resolveType ty
  return (fmap rebuild_field ty')
  where
    rebuild_field t = FieldDef mutability t name

resolveRecordDef :: RecordDef Parsed -> NR ()
resolveRecordDef record = do
  -- Create the new record's fields
  let num_params = length $ recordParams record
  fields <- enterNonRec $ do
    mapM defineTypeParam $ recordParams record
    mapM resolveFieldDef $ recordFields record
    
  defineRecord (recordName record) num_params fields

resolveDef :: Def Parsed -> NR (Maybe (Def Typed))
resolveDef def = 
  case def
       of FunctionDefEnt fdef ->
            fmap (Just . FunctionDefEnt) $ resolveFunctionDef True fdef
          DataDefEnt ddef ->
            fmap (Just . DataDefEnt) $ resolveDataDef ddef
          RecordDefEnt rdef -> do
            resolveRecordDef rdef
            return Nothing

-- | Resolve a set of top-level definitions
resolveTopLevelDefs :: [Def Parsed] -> NR [Def Typed]
resolveTopLevelDefs defs = fmap catMaybes $ mapM resolveDef defs

resolveExternType :: ExternType Parsed -> NR (ExternType Typed)
resolveExternType (ExternProcedure domain range) = do
  domain' <- mapM resolveType0 domain
  range' <- mapM resolveType0 range
  return $ ExternProcedure domain' range'

resolveExternType (ExternFunction domain range) = do
  domain' <- mapM resolveType0 domain
  range' <- mapM resolveType0 range
  return $ ExternFunction domain' range'

resolveExternType (ExternData pt) = return (ExternData pt)

-------------------------------------------------------------------------------
-- External variables

-- | Resolve a set of external variable declarations.  The variables are 
-- added to the current scope.
withExternalVariables :: [ExternDecl Parsed] -> NR [Def Typed]
                      -> NR ([LL.Import], [Def Typed])
withExternalVariables edefs m = do 
  external_defs <- mapM defineExternalVar edefs
  let evars = [LL.importVar i | (_, _, i) <- external_defs]

  -- Process all definitions
  processed_defs <- with_evars evars m
  
  -- Check that all definitions of exported variable are consistent
  let defs_map = Map.fromList [(def_var d, d) | d <- processed_defs]
        where
          def_var (DataDefEnt d) = dataName d
          def_var (FunctionDefEnt d) = functionName d

  mapM_ (checkExternalVar defs_map) external_defs
  return ([i | (_, _, i) <- external_defs], processed_defs)
  where
    -- Save the external variables in the environment for later lookup
    with_evars evars m = NR $ \nrenv env errs ->
      let nrenv' = nrenv {externalVariables = evars ++ externalVariables nrenv}
      in runNR m nrenv' env errs

-- | Verify that the external variable declaration is consistent with the
--   imported variable declaration and the actual definition.
--
--   Check the types of the declarations. 
checkExternalVar :: Map.Map LL.Var (Def Typed) 
                 -> (ExternDecl Typed, Bool, LL.Import)
                 -> NR ()
checkExternalVar defs_map (edef, is_builtin, impent) = do
  -- If it's a builtin variable, compare the definition to the import entity.
  -- Otherwie, 'impent' and 'edef' were created from the same declaration so
  -- they will be consistent.
  when is_builtin compare_to_import
  
  -- If it was defined in this module, compare the definition.
  case Map.lookup (LL.importVar impent) defs_map of
    Just def -> compare_to_def def
    Nothing -> return ()
  where
    compare_to_import =
      case (externType edef, impent)
      of (ExternProcedure domain range, LL.ImportPrimFun _ imptype _) ->
           let domain' = map convertToValueType domain
               range' = map convertToValueType range
               exttype = primFunctionType domain' range'
               doc = hang (text "expected") 9 (LL.pprFunctionType imptype) $$
                     hang (text "got") 9 (LL.pprFunctionType exttype)
           in throwErrorMaybe $
              if imptype == exttype then Nothing else incompatible_builtin doc
         (ExternFunction domain range, LL.ImportClosureFun ep _) ->
           let domain' = map convertToValueType domain
               range' = map convertToValueType range
               exttype = closureFunctionType domain' range'
               doc = hang (text "expected") 9 (LL.pprFunctionType $ LL.entryPointsType ep) $$
                     hang (text "got") 9 (LL.pprFunctionType exttype)
           in throwErrorMaybe $
              if LL.entryPointsType ep == exttype
              then Nothing
              else incompatible_builtin doc
         (ExternData etype, LL.ImportData v _) ->
           let doc = hang (text "expected") 9 (LL.pprPrimType etype) $$
                     hang (text "got") 9 (LL.pprValueType $ LL.varType v)
           in throwErrorMaybe $
              if PrimType etype == LL.varType v
              then Nothing
              else incompatible_builtin doc
         _ -> throwErrorMaybe (incompatible_builtin (text "Object has wrong class"))

    compare_to_def (FunctionDefEnt d)
      | functionIsProcedure d, 
        ExternProcedure e_domain e_range <- externType edef =
          compare_function_type e_domain e_range
      | not (functionIsProcedure d),
        ExternFunction e_domain e_range <- externType edef =
          compare_function_type e_domain e_range
      | otherwise =
          throwErrorMaybe incompatible_definition
      where
        compare_function_type e_domain e_range =
          let d_domain = [convertToValueType t
                         | Parameter t _ <- functionParams d]
              d_range = map convertToValueType $ functionReturns d
              e_domain' = map convertToValueType e_domain
              e_range' = map convertToValueType e_range
          in throwErrorMaybe $
             if d_domain == e_domain' && d_range == e_range'
             then Nothing
             else incompatible_definition

    compare_to_def (DataDefEnt d)
      | ExternData e_type <- externType edef =
        throwErrorMaybe $
        if dataType d == e_type
        then Nothing
        else incompatible_definition

    incompatible_definition =
      Just $ "Incompatible definition of exported variable '" ++
      labelLocalNameAsString (fromJust $ LL.varName $ LL.importVar impent) ++ "'"
      
    incompatible_builtin details =
      Just $ "Incompatible definition of built-in variable '" ++
      labelLocalNameAsString (fromJust $ LL.varName $ LL.importVar impent) ++ "'\n" ++
      show details

-- | Resolve an external variable declaration.
--   No variables are defined.
--
--   Returns the resolved declaration and an imported variable object.
--   Also returns a boolean that's @True@ if a builtin variable was used.
resolveExternDecl :: ExternDecl Parsed
                  -> NR (ExternDecl Typed, Bool, LL.Import)
resolveExternDecl decl = do
  let label = externLabel decl
  let primtype = externTypePrimType (externType decl)
  
  -- Resolve the type
  new_type <- resolveExternType (externType decl)
  
  -- If it's a builtin variable, get the imported variable.
  -- Otherwise, create an Import structure.
  (is_builtin, impent) <-
    case getBuiltinImportByLabel label
    of Just builtin_impent -> do
         check_external_name label builtin_impent
         return (True, builtin_impent)
       Nothing -> do
         impent <- createImport label new_type
         return (False, impent)
  
  let new_decl =
        case decl
        of ExternDecl _ l -> ExternDecl new_type l
           ImportDecl _ l _ -> ImportDecl new_type l (LL.importVar impent)

  return (new_decl, is_builtin, impent)
  where
    -- Verify that the given labels match
    check_external_name label impent =
      case LL.varName (LL.importVar impent)
      of Just impname ->
           if impname /= label
           then error $ "Incompatible definition of variable '" ++
                labelLocalNameAsString label ++ "'"
           else return ()
         Nothing -> internalError "resolveExternDecl: No label"

createImport label new_type =
  case new_type
  of ExternProcedure domain range -> do
       let ty = PrimType (externTypePrimType new_type)
           function_type = primFunctionType
                           (map convertToValueType domain)
                           (map convertToValueType range)
       v <- LL.newExternalVar label ty
       return $ LL.ImportPrimFun v function_type Nothing
     ExternFunction domain range -> do
       let ty = PrimType (externTypePrimType new_type)
           function_type = closureFunctionType
                           (map convertToValueType domain)
                           (map convertToValueType range)
       v <- LL.newExternalVar label ty
       ep <- mkGlobalEntryPoints function_type label v
       return $ LL.ImportClosureFun ep Nothing
     ExternData primtype -> do
       v <- LL.newExternalVar label (PrimType primtype)
       return $ LL.ImportData v Nothing

-- | Define an external variable.
--
-- If the variable name and module matches a built-in variable, then use that
-- variable; otherwise, create a new variable.
--    
-- If the variable belongs outside the current module, then define it here.
-- Otherwise, the variable must be defined later in the module.
defineExternalVar :: ExternDecl Parsed
                  -> NR (ExternDecl Typed, Bool, LL.Import)
defineExternalVar decl = do
  (resolved_decl, is_builtin, impent) <- resolveExternDecl decl
  let var = LL.importVar impent
      ty  = externTypePrimType $ externType decl
  -- If the variable is not in the current module, then define it.
  -- Otherwise, it will be defined later.
  current_module <- getSourceModuleName
  let mod = case LL.varName var
            of Just n -> labelModule n
               Nothing -> internalError "defineExternalVar"
  when (mod /= current_module) $ defineVar var (PrimT ty)
  return (resolved_decl, is_builtin, impent)

-------------------------------------------------------------------------------
-- Entry point

typeInferModule :: FilePath
                -> ModuleName
                -> [ExternDecl Parsed]
                -> [Def Parsed]
                -> IO ([LL.Import], [Def Typed])
typeInferModule module_path module_name externs defs = do
  type_synonym_ids <- newIdentSupply
  withTheLLVarIdentSupply $ \var_ids -> do
    let ctx = NREnv var_ids type_synonym_ids [] module_name
        global_env = Env 0 [predefinedScope]
    
        -- Start out in the global scope.
        -- Create the external variables, then process each top-level
        -- definition.
        generate_module =
          enterRec $ withExternalVariables externs $ resolveTopLevelDefs defs

    (return_data, _, errs) <- runNR generate_module ctx global_env id

    case errs [] of
      [] -> return return_data
      xs -> do mapM_ putStrLn xs
               fail "Errors detected while parsing input"

predefinedScope = NonRecScope $
                  Map.fromList [("array", template arraycon),
                                ("const_array", template constarraycon),
                                ("bytes", template bytescon)]
  where
    template = TypeEntry . NamedT . TemplateT
    
    arraycon = Parameterized (Just 2) $ \[size_arg, type_arg] ->
      ArrayT Mutable (fromExprArg size_arg) (fromTypeArg type_arg)

    constarraycon = Parameterized (Just 2) $ \[size_arg, type_arg] ->
      ArrayT Constant (fromExprArg size_arg) (fromTypeArg type_arg)
    
    bytescon = Parameterized (Just 2) $ \[size_arg, align_arg] ->
      BytesT (fromExprArg size_arg) (fromExprArg align_arg)
