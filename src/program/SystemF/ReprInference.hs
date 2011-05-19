{-| Infer data structure representations.

The input program uses the pure type system.  All values are boxed
and have kind @box@.  The output program uses the specification type
system, in which values inhabit four different kinds: @val@, @box@,
@bare@, and @write@.

-}

{-# LANGUAGE FlexibleInstances, Rank2Types, GeneralizedNewtypeDeriving #-}
module SystemF.ReprInference(representationInference)
where

import Control.Monad.Reader
import Data.Monoid
import qualified Data.IntMap as IntMap
import Debug.Trace

import Text.PrettyPrint.HughesPJ

import Common.MonadLogic
import Common.Identifier
import Common.Supply
import Common.Error
import Builtins.Builtins
import Type.Compare
import Type.Environment
import Type.Eval
import Type.Rename
import Type.Type
import SystemF.ReprDict
import SystemF.Syntax
import SystemF.Print
import SystemF.MemoryIR
import qualified SystemF.PrintMemoryIR as PrintMemoryIR
import qualified SystemF.TypecheckSF as TypecheckSF
import qualified SystemF.TypecheckMem as TypecheckMem

import Globals
import GlobalVar

-- | The representation inference monad.
--
--   Specification types are tracked for variables that are in scope.
--   New variables can be created.
newtype RI a = RI {unRI :: ReaderT RIEnv IO a}
             deriving(Functor, Monad)

data RIEnv =
  RIEnv
  { riVarSupply :: {-#UNPACK#-}!(IdentSupply Var)

    -- | The specification type environment
  , riTypeEnv :: TypeEnv
  , riDictEnv :: MkDictEnv
  , riIntIndexEnv :: IntIndexEnv

    -- | The system F type environment
  , riSystemFTypeEnv :: TypeEnv
  }

instance MonadIO RI where
  liftIO m = RI $ liftIO m

instance Supplies RI (Ident Var) where
  fresh = RI $ ReaderT $ \env -> supplyValue (riVarSupply env)

instance TypeEnvMonad RI where
  getTypeEnv = RI $ asks riTypeEnv
  assume v t m = RI $ local insert_type (unRI m)
    where
      insert_type env = env {riTypeEnv = insertType v t $ riTypeEnv env}

instance ReprDictMonad RI where
  getVarIDs = RI $ asks riVarSupply
  getDictEnv = RI $ asks riDictEnv
  getIntIndexEnv = RI $ asks riIntIndexEnv
  localDictEnv f (RI m) = RI $ local f_dict m
    where
      f_dict env = env {riDictEnv = f $ riDictEnv env}
  localIntIndexEnv f (RI m) = RI $ local f_intindex m
    where
      f_intindex env = env {riIntIndexEnv = f $ riIntIndexEnv env}

instance EvalMonad RI

-- | Infer the type of a System F expression.  The inferred type
--   is the System F type, not the specification type.
riInferExpType :: ExpSF -> RI Type
riInferExpType expression = RI $ ReaderT $ \env -> do
  TypecheckSF.inferExpType (riVarSupply env) (riSystemFTypeEnv env) expression

riLookupType :: Var -> RI Type
riLookupType v = askTypeEnv lookup_type
  where
    lookup_type env =
      case lookupType v env
      of Just rt -> rt
         _ -> internalError $ "riLookupType: not found: " ++ show v

riLookupDataCon :: Var -> RI DataConType
riLookupDataCon v = askTypeEnv lookup_type
  where
    lookup_type env =
      case lookupDataCon v env
      of Just rt -> rt
         _ -> internalError $ "riLookupDataCon: not found: " ++ show v

-- | Add a type to the System F type environment
assumeSFType :: Var -> Type -> RI a -> RI a
assumeSFType v t m = RI $ local insert_type (unRI m)
  where
    insert_type env =
      env {riSystemFTypeEnv = insertType v t $ riSystemFTypeEnv env}

-- | Add a System F type and a specification type to the environment.
--
--   Variables bound in the program are added to the environment, since we
--   may need to infer either the System F type or the specification type.
--
--   For variables bound in /types/, we don't need the System F type
--   environment.  New variables created by the translation (in coercions,
--   for example) don't have System F types.
assumeValueTypes :: Var -> Type -> Type -> RI a -> RI a
assumeValueTypes v sf_type spec_type m =
  assume v spec_type $ assumeSFType v sf_type m

-- | Add a System F type and a specification type to the environment
--
--   Variables bound in the program are added to the environment, since we
--   may need to infer either the System F type or the specification type.
--
--   For variables bound in /types/, we don't need the System F type
--   environment.  New variables created by the translation (in coercions,
--   for example) don't have System F types.
assumeTypeKinds :: Var -> Kind -> Kind -> RI a -> RI a
assumeTypeKinds a sf_kind spec_kind m =
  assume a spec_kind $ assumeSFType a sf_kind m

-------------------------------------------------------------------------------

-- | Given a type in WHNF, put the type into its natural representation by
--   removing type constructors that convert representations.
--
--   This function is idempotent, so we can use 'compareTypes' to check
--   whether 'stripReprConversions' has done anything.
stripReprConversions :: EvalMonad m => Type -> m Type
stripReprConversions t = strip False t
  where
    strip changed t =
      case fromVarApp t
      of Just (op, [arg])
           | -- Type functions
             op `isPyonBuiltin` the_BoxedType ||
             op `isPyonBuiltin` the_BareType ||
             -- Special constructor
             op `isPyonBuiltin` the_Writer ||
             -- Adapter type constructors
             op `isPyonBuiltin` the_Boxed ||
             op `isPyonBuiltin` the_StoredBox ||
             op `isPyonBuiltin` the_Stored ->
               strip True arg
         _ -> if changed
              then stripReprConversions =<< reduceToWhnf t
              else return t

-- | Get the natural kind of a type.  The type is in WHNF and has had
--   adapters removed from it, so the outermost term is a data constructor,
--   function, forall'd type, or Any.
--
--   If the outermost term is a type variable, its natural kind cannot be
--   determined, so 'Nothing' is returned.
coercionKind :: TypeEnv -> Type -> Maybe BaseKind
coercionKind tenv natural_t =
  case fromVarApp natural_t
  of Just (op, args)
       | Just dtype <- lookupDataType op tenv ->
           Just $ dataTypeKind dtype
       | otherwise -> Nothing
     Nothing ->
       case natural_t
       of FunT {} -> Just BoxK
          AllT {} -> Just BoxK
          _ -> internalError "coercionKind: Not implemented for this type"

-- | Given two types returned by 'stripReprConversions',
--   determine the natural kind of the most specific head type.
--
--   If both types have variables or functions as their outermost term, 
--   then Nothing is returned.
mostSpecificNaturalHeadKind :: EvalMonad m => Type -> Type -> m BaseKind
mostSpecificNaturalHeadKind t1 t2 = do
  tenv <- getTypeEnv
  getMsnk tenv t1 $ getMsnk tenv t2 $ unknown_type
  where
    getMsnk tenv t or_else =
      case coercionKind tenv t of
        Just k  -> return k
        Nothing -> or_else

    -- If the type is unknown, prefer the bare representation
    unknown_type = return BareK

-------------------------------------------------------------------------------

-- | The mode in which to translate a type.
--
--   In most cases, types are translated using 'NaturalMode', which is
--   expected to be more efficient.  However, in a type application, the
--   argument is translated using 'CanonicalMode', which ensures a unique
--   translation of each input type.  'CanonicalMode' translates functions
--   to always take boxed arguments and return a boxed value.  It is never
--   necessary to coerce under type application if a type was translated
--   using 'CanonicalMode'.
data TypeMode =
    NaturalMode                   -- ^ Natural representation
  | CanonicalMode                 -- ^ Canonical representation

-- | Convert a System F kind to a representation-specific kind.
cvtKind :: Kind -> Kind
cvtKind k =
  case k
  of VarT v
       | v == boxV      -> bareT
       | v == intindexV -> intindexT
     k1 `FunT` k2       -> cvtKind k1 `FunT` cvtKind k2
     _ -> internalError "cvtKind: Unexpected kind"

-- | Coerce a type by applying wrapper type constructors.
coerceType :: Kind              -- ^ Given kind
           -> Kind              -- ^ Expected kind
           -> Type              -- ^ Given type
           -> RI Type           -- ^ Expected type
coerceType g_k e_k g_t =
  case (e_k, g_k)
  of (VarT e_kv, VarT g_kv)
       | e_kv == g_kv -> return g_t -- No need to coerce
       | e_kv == valV && g_kv == bareV ->
           case fromVarApp g_t
           of Just (op, [arg]) | op `isPyonBuiltin` the_Stored -> return arg
              _ -> internalError "coerceType"
       | e_kv == valV && g_kv == boxV ->
           case fromVarApp g_t
           of Just (op, [arg]) | op `isPyonBuiltin` the_BoxedType ->
                case fromVarApp arg
                of Just (op, [arg2]) | op `isPyonBuiltin` the_Stored -> return arg2
                   _ -> internalError "coerceType"
              _ -> internalError "coerceType"
       | e_kv == boxV && g_kv == valV ->
           return $
           varApp (pyonBuiltin the_BoxedType)
           [varApp (pyonBuiltin the_Stored) [g_t]]
       | e_kv == boxV && g_kv == bareV ->
           return $ boxedType g_t
       | e_kv == bareV && g_kv == valV ->
           return $varApp (pyonBuiltin the_Stored) [g_t]
       | e_kv == bareV && g_kv == boxV ->
           return $ bareType g_t
     (e_dom `FunT` e_rng, g_dom `FunT` g_rng)
       | sameKind e_dom g_dom && sameKind e_rng g_rng ->
           return g_t -- No need to coerce
       | otherwise -> do
           param <- newAnonymousVar TypeLevel
           coerced_param <- coerceType e_dom g_dom (VarT param)
           coerced_result <- coerceType g_rng e_rng $ AppT g_t coerced_param
           return $ LamT (param ::: e_dom) coerced_result

sameKind (VarT k1) (VarT k2) = k1 == k2
sameKind (k1 `FunT` k2) (k3 `FunT` k4) =
  sameKind k1 k3 && sameKind k2 k4
sameKind _ _ = False

-- | Type coercions
--
-- * writeType : bare -> write
-- * boxedType : bare -> box
-- * bareType  : box  -> bare
writeType, boxedType, bareType :: Type -> Type
writeType t = varApp (pyonBuiltin the_Writer) [t]
boxedType t = varApp (pyonBuiltin the_BoxedType) [t]
bareType t  = varApp (pyonBuiltin the_BareType) [t]

-- | Convert a System F type to its natural representation
cvtNaturalType :: Type -> RI (Type, Kind)
cvtNaturalType = cvtType NaturalMode

-- | Convert a System F type to canonical representation
cvtCanonicalType :: Type -> RI (Type, Kind)
cvtCanonicalType = cvtType CanonicalMode

-- | Convert a parameter or return type to boxed form
cvtCanonicalParamType  :: Type -> RI Type
cvtCanonicalParamType t = do
  (t, k) <- cvtCanonicalType t
  coerceType k boxT t

cvtCanonicalReturnType  :: Type -> RI Type
cvtCanonicalReturnType = cvtCanonicalParamType

-- | Convert a System F type to the preferred representation for
--   function parameters
cvtParamType :: Type -> RI (Type, Kind)
cvtParamType t = cvtNaturalType t

cvtReturnType :: Type -> RI (Type, Kind)
cvtReturnType t = do
  (t', k) <- cvtNaturalType t
  case k of
    VarT v | v == bareV -> return (writeType t', boxT)
    _ -> return (t', k)

-- | Convert a System F type to a variable type for a let-bound variable.
--   The type will be in kind @val@ or @box@.
cvtLocalType :: Type -> RI (Type, Kind)
cvtLocalType t = do
  (t', k) <- cvtNaturalType t
  case k of
    VarT v | v == bareV -> return (boxedType t', boxT)
    _ -> return (t', k)

-- | Helper function for 'cvtType'.  If mode is 'CanonicalMode', coerce to
--   a boxed kind.
wrapForMode :: TypeMode -> Type -> Kind -> RI (Type, Kind)
wrapForMode NaturalMode   t k = return (t, k)
wrapForMode CanonicalMode t k = do
  t' <- coerceType k boxT t
  return (t', boxT)

-- | Convert a System F type to a representation type.
--
--   If converting in 'CanonicalMode', function types always take a parameter
--   and return with @box@ kind.
--   In 'NaturalMode', the parameter and return types have the preferred kind
--   for its representation.
cvtType :: TypeMode -> Type -> RI (Type, Kind)
cvtType mode (VarT v) = do
  k <- riLookupType v
  return (VarT v, k)

cvtType mode (AppT t1 t2) = do
  (t1', t1_k) <- cvtType mode t1
  case t1_k of
    dom_k `FunT` rng_k -> do
      -- Convert and coerce argument type
      (t2', t2_k) <- cvtType mode t2
      t2'' <- coerceType t2_k dom_k t2'
      return (AppT t1' t2'', rng_k)
    _ -> internalError "cvtNaturalType: Invalid type"

cvtType mode (t1 `FunT` t2) = do
  -- Function type
  dom <- case mode 
         of NaturalMode   -> fmap fst $ cvtParamType t1
            CanonicalMode -> cvtCanonicalParamType t1
  rng <- case mode
         of NaturalMode   -> fmap fst $ cvtReturnType t2
            CanonicalMode -> cvtCanonicalReturnType t2
  return (dom `FunT` rng, boxT)

cvtType mode (AllT (a ::: t1) t2) = do
  -- Forall type
  let dom = cvtKind t1
  rng <- assume a dom $ fmap fst $ cvtType mode t2 
  return (AllT (a ::: dom) rng, boxT)

-- | Convert a System F type to its natural representation.
--   Try to simplify the resulting type expression.
cvtNormalizeNaturalType :: Type -> RI (Type, Kind)
cvtNormalizeNaturalType t = do
  (t', k) <- cvtNaturalType t
  t'' <- normalize t'
  liftIO $ print $ text "Convert NT" <+> (pprType t $$ pprType t'')
  return (t'', k)

-- | Convert a System F type to its canonical representation.
--   Try to simplify the resulting type expression.
cvtNormalizeCanonicalType :: Type -> RI (Type, Kind)
cvtNormalizeCanonicalType t = do
  (t', k) <- cvtCanonicalType t
  t'' <- normalize t'
  liftIO $ print $ text "Convert CT" <+> (pprType t $$ pprType t'')
  return (t'', k)

-- | Convert a System F type to the preferred representation for a 
--   local variable.
--   Try to simplify the resulting type expression.
cvtNormalizeLocalType :: Type -> RI (Type, Kind)
cvtNormalizeLocalType t = do
  (t', k) <- cvtLocalType t
  t'' <- normalize t'
  liftIO $ print $ text "Convert LT" <+> (pprType t $$ pprType t'')
  return (t'', k)

-- | Convert a System F type to the preferred representation for a 
--   function parameter.
--   Try to simplify the resulting type expression.
cvtNormalizeParamType :: Type -> RI (Type, Kind)
cvtNormalizeParamType t = do
  (t', k) <- cvtParamType t
  t'' <- normalize t'
  liftIO $ print $ text "Convert PT" <+> (pprType t $$ pprType t'')
  return (t'', k)

-- | Convert a System F type to the preferred representation for a 
--   function return.
--   Try to simplify the resulting type expression.
cvtNormalizeReturnType :: Type -> RI (Type, Kind)
cvtNormalizeReturnType t = do
  (t', k) <- cvtReturnType t
  t'' <- normalize t'
  liftIO $ print $ text "Convert RT" <+> (pprType t $$ pprType t'')
  return (t'', k)

-------------------------------------------------------------------------------
-- Coercing expressions

-- | A coercion.  Given an expression and a continuation that uses the
--   coerced expression to create a new expression, create an application of
--   the continuation to the coerced expression.
--
--   Coercions may wrap the producer of the coerced value (the expression)
--   and/or the consumer of the coerced value (the continuation's result).
data Coercion =
    IdCoercion    
  | Coercion !(forall a. (ExpM -> RI (ExpM, a)) -> ExpM -> RI (ExpM, a))

-- | Coercions form a monoid under composition.
--   The composition @d `mappend` c@ applies coercion @c@, then coercion @d@.
instance Monoid Coercion where
  mempty = IdCoercion
  mappend IdCoercion c = c
  mappend c IdCoercion = c
  mappend (Coercion g) (Coercion f) =
    Coercion (\k e -> f (g k) e)

-- | Coerce @val -> write@ using the @stored@ constructor.
--   The argument is the @val@ type.
toStoredCoercion :: Type -> Coercion
toStoredCoercion ty = Coercion co
  where
    co k e = k (ExpM $ AppE defaultExpInfo stored_op [TypM ty] [e])
    stored_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_stored)

-- | Coerce @bare -> val@ using the @stored@ constructor.
--   The argument is the @val@ type.
fromStoredCoercion :: Type -> Coercion
fromStoredCoercion ty = Coercion co
  where
    co k e = do
      val_var <- newAnonymousVar ObjectLevel
      (expr, x) <- k (ExpM $ VarE defaultExpInfo val_var)
      
      -- Create a case statement
      let alt = AltM $ Alt { altConstructor = pyonBuiltin the_stored
                           , altTyArgs = [TypM ty]
                           , altExTypes = []
                           , altParams = [memVarP (val_var ::: ty)]
                           , altBody = expr}
          cas = ExpM $ CaseE defaultExpInfo e [alt]
      return (cas, x)

-- | Coerce @bare -> box@ using the @convertToBoxed@ function.
--   The argument is the @bare@ type.
toBoxedTypeCoercion :: Type -> Coercion
toBoxedTypeCoercion ty = Coercion co
  where
    co k e = do
      dict <- withReprDict ty return
      k (ExpM $ AppE defaultExpInfo box_op [TypM ty] [dict, e])
    box_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_convertToBoxed)

-- | Coerce @box -> bare@ using the @convertToBare@ function.
--   The argument is the @bare@ type.
toBareTypeCoercion :: Type -> Coercion
toBareTypeCoercion ty = Coercion co
  where
    co k e = do
      dict <- withReprDict ty return
      k (ExpM $ AppE defaultExpInfo bare_op [TypM ty] [dict, e])
    bare_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_convertToBare)

-- | Coerce @read -> write@ using the @copy@ function.
--   The argument is the @bare@ type.
copyCoercion :: Type -> Coercion
copyCoercion ty = Coercion co
  where
    co k e = do
      dict <- withReprDict ty return
      k (ExpM $ AppE defaultExpInfo copy_op [TypM ty] [dict, e])
    copy_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_copy)

-- | Coerce @write -> bare@ by assigning to a temporary variable, then
--   reading from the temporary variable.
--   The argument is the @bare@ type.
--    
--   Note that the data is put into a box, /not/ converted to a boxed 
--   representation.

-- The generated code is:
-- let boxed_var = Boxed e
-- in case boxed_var
--    of Boxed read_var. k read_var
writeLocalCoercion :: Type -> Coercion
writeLocalCoercion ty = Coercion co
  where
    co k e = do
      boxed_var <- newAnonymousVar ObjectLevel
      read_var <- newAnonymousVar ObjectLevel
      (expr, x) <- k (ExpM $ VarE defaultExpInfo read_var)
      
      let rhs = ExpM $ AppE defaultExpInfo box_op [TypM ty] [e]
          expr_alt = AltM $ Alt { altConstructor = pyonBuiltin the_boxed
                                , altTyArgs = [TypM ty]
                                , altExTypes = []
                                , altParams = [memVarP (read_var ::: ty)]
                                , altBody = expr}
          body = ExpM $ CaseE defaultExpInfo
                 (ExpM $ VarE defaultExpInfo boxed_var)
                 [expr_alt]
          pattern = memVarP (boxed_var ::: box_type)
          local_expr = ExpM $ LetE defaultExpInfo pattern rhs body
      return (local_expr, x)
    box_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_boxed)
    box_type = varApp (pyonBuiltin the_Boxed) [ty]

-- | Create a coercion that coerces from one specification function
--   type to another specification function type.
--
--   The coercion is a lambda function wrapping the argument.
functionCoercion :: [Binder] -> [Type] -> Type
                 -> [Binder] -> [Type] -> Type
                 -> Coercion
functionCoercion g_tydom g_dom g_rng e_tydom e_dom e_rng
  | length g_tydom /= length e_tydom ||
    length g_dom /= length e_dom =
      internalError "functionCoercion: Mismached function types"
  | null g_tydom && null g_dom =
      internalError "functionCoercion: Not a function type"
  | otherwise = Coercion co
  where
    co k given_e = do
      coerced_e <-
        -- Insert expected function types into environment
        assume_ty_params $ withMany define_param e_dom $ \e_params -> do

          -- Compute result type and coerce arguments
          let given_type = forallType g_tydom (funType g_dom g_rng)
            
          -- Expected parameters will be passed as type arguments
          let type_args = [(VarT a, k) | a ::: k <- e_tydom]
              value_args = [(ExpM $ VarE defaultExpInfo (patMVar' p),
                             patMType p)
                           | p <- e_params]

          -- Create a call to the original function
          (call, return_type) <-
            reprApply given_e given_type type_args value_args
          body <- coerceExpToReturnType return_type e_rng call

          -- Create a lambda function
          let fun_ty_args = [TyPatM d | d <- e_tydom]
              fun_ret = TypM e_rng
              fun =
                FunM $ Fun defaultExpInfo fun_ty_args e_params fun_ret body
          return $ ExpM $ LamE defaultExpInfo fun

      -- Pass the coerced expression to the continuation
      k coerced_e

    -- Add the expected function type parameters to the environment
    assume_ty_params m = foldr assumeBinder m e_tydom

    -- Define a pattern for a value parameter
    define_param ty k = do
      v <- newAnonymousVar ObjectLevel
      assume v ty $ k (memVarP (v ::: ty))

-- | Apply a coercion to an expression.
coerceExp :: Coercion -> ExpM -> (ExpM -> RI (ExpM, a)) -> RI (ExpM, a)
coerceExp IdCoercion   e k = k e
coerceExp (Coercion f) e k = f k e

-- | Apply coercions to expressions.
coerceExps :: [Coercion] -> [ExpM] -> ([ExpM] -> RI (ExpM, a)) -> RI (ExpM, a)
coerceExps (co:cos) (e:es) k =
  coerceExp co e $ \e' -> coerceExps cos es $ \es' -> k (e':es')

coerceExps [] [] k = k []

coerceExps _ _ _ = internalError "coerceExps: List length mismatch"

-- | Create a coercion that coerces a value from the given type to the
--   expected type.
coercion :: EvalMonad m =>
            Type                -- ^ Given type
         -> Type                -- ^ Expected type
         -> m Coercion          -- ^ Computes the coercion
coercion g_type e_type = do
  tenv <- getTypeEnv
  whnf_g_type <- reduceToWhnf g_type
  whnf_e_type <- reduceToWhnf e_type
  let g_kind = toBaseKind $ typeKind tenv whnf_g_type
      e_kind = toBaseKind $ typeKind tenv whnf_e_type
  
  types_equal <-
    if g_kind == e_kind
    then compareTypes whnf_e_type whnf_g_type
    else return False
  
  -- If types are equal, then coercion is unnecessary
  if types_equal then return IdCoercion else do

    -- Determine the representation to use while doing value coercion.
    -- If the representation is unknown, that means we do not know the
    -- outermost data type constructor.  In that case, coercion is impossible
    -- so the types should already be equal.
    natural_g_type <- stripReprConversions whnf_g_type
    natural_e_type <- stripReprConversions whnf_e_type
    coerce_kind <- mostSpecificNaturalHeadKind natural_g_type natural_e_type

    liftIO $ print $ text "Coerce " <+>
      (pprType whnf_g_type $$
       text "to" <+> pprType whnf_e_type $$
       text "via" <+> text (show coerce_kind) $$
       text (show g_kind) <+> text (show e_kind))
  
    -- Create a coercion.  Coerce to the natural representation,
    -- then coerce the value, then coerce to the output representation.
    co1 <- representationCoercion natural_g_type coerce_kind g_kind coerce_kind
    co2 <- valueCoercion coerce_kind natural_g_type natural_e_type
    co3 <- representationCoercion natural_e_type coerce_kind coerce_kind e_kind
    return (co3 `mappend` co2 `mappend` co1)

-- | Compute the appropriate coercion to coerce an object from the
--   given representation to the expected representation.
--  
--   The type argument is in WHNF.
representationCoercion :: EvalMonad m =>
                          Type -> BaseKind -> BaseKind -> BaseKind
                       -> m Coercion
representationCoercion natural_ty natural_kind g_kind e_kind =
  case (g_kind, e_kind)
  of _ | g_kind == e_kind -> return IdCoercion
     (ValK, WriteK)       -> return $ toStoredCoercion natural_ty
     (ValK, _)            -> coerce_via WriteK
     (BoxK, WriteK)       -> return $ toBareTypeCoercion bare_ty
     (BoxK, ValK)         -> coerce_via WriteK
     (BoxK, BareK)        -> coerce_via WriteK
     (BareK, ValK)        -> return $ fromStoredCoercion natural_ty
     (BareK, BoxK)        -> return $ toBoxedTypeCoercion bare_ty
     (BareK, WriteK)      -> return $ copyCoercion bare_ty
     (WriteK, ValK)       -> coerce_via BareK
     (WriteK, BoxK)       -> coerce_via BareK
     (WriteK, BareK)      -> return $ writeLocalCoercion bare_ty
     _                    -> invalid_coercion
  where
    invalid_coercion =
      internalError $ "Attempt to generate invalid coercion: " ++
      show g_kind ++ " -> " ++ show e_kind

    -- The bare object type corresponding to natural_ty
    bare_ty =
      case natural_kind
      of ValK  -> varApp (pyonBuiltin the_Stored) [natural_ty]
         BareK -> natural_ty
         BoxK  -> varApp (pyonBuiltin the_BareType) [natural_ty]

    -- Coerce to another kind, then coerce to final kind
    coerce_via k = do
      co1 <- representationCoercion natural_ty natural_kind g_kind k
      co2 <- representationCoercion natural_ty natural_kind k e_kind
      return $ co2 `mappend` co1

-- | Compute the appropriate coercion to coerce an object from the
--   given type to the expected type.  The given and expected types have
--   the same representation.
--  
--   The type argument is in WHNF.
valueCoercion :: EvalMonad m =>
                 BaseKind -> Type -> Type -> m Coercion
valueCoercion kind g_type e_type = do
  types_equal <- compareTypes g_type e_type
  if types_equal then return IdCoercion else
    let (g_tydom, g_dom, g_rng) = fromForallFunType g_type
        (e_tydom, e_dom, e_rng) = fromForallFunType e_type
    in if not (null g_tydom) || not (null g_dom)
       then return $ functionCoercion g_tydom g_dom g_rng e_tydom e_dom e_rng
       else traceShow (pprType g_type $$ pprType e_type) $ internalError "valueCoercion: Not implemented for this type"

coerceExpAtType :: Type -> Type -> ExpM -> (ExpM -> RI (ExpM, a))
                -> RI (ExpM, a)
coerceExpAtType g_type e_type e k = do
  co <- coercion g_type e_type
  coerceExp co e k

-- | Coerce an expression and return the result.  This is only valid for
--   return types, because we can't put a case statement around the consumer
--   when using this coercion strategy.
coerceExpToReturnType :: Type -> Type -> ExpM -> RI ExpM
coerceExpToReturnType g_type e_type e =
  fmap fst $ coerceExpAtType g_type e_type e $ \e' -> return (e', ())

-- | Add a variable to the dictionary environment if its type indicates that
--   it's a dictionary.
assumeReprDict v ty m =
  case fromVarApp ty
  of Just (op, [arg])
       | op `isPyonBuiltin` the_Repr ->
           saveReprDict arg (ExpM $ VarE defaultExpInfo v) m
       | op `isPyonBuiltin` the_IndexedInt ->
           saveIndexedInt arg (ExpM $ VarE defaultExpInfo v) m
     _ -> m

-------------------------------------------------------------------------------
-- Function application

-- | A type argument to an application.  The type has been converted to
--   a specification type.  The type's kind is passed along with it.
type TypeArgument = (Type, Kind)

-- | Result of applying a function to type and value arguments.
--   The result contains the operator and type arguments.  It must be applied
--   to value arguments in a separate step.
--
--   Application of some arguments may fail because the function has to 
--   be coerced.  Those arguments will be returned unmodified.
data AppResult =
  AppResult
  { -- | The applied expression, except for value arguments which must be
    --   supplied separately.  The /coerced/ arguments will be passed to this
    --   function.
    appliedExpr            :: [ExpM] -> RI ExpM

    -- | The result of the applied expression
  , appliedReturnType      :: Type

    -- | Coercions that should be applied to value arguments
    --   (in reverse order, relative to arguments)
  , appliedCoercions       :: [Coercion]
  }

appResult :: ExpM -> Type -> AppResult
appResult e ty = AppResult { appliedExpr       = mk_expr
                           , appliedReturnType = ty
                           , appliedCoercions  = []}
  where
    mk_expr [] = return e
    mk_expr _  = internalError "appResult: Wrong number of arguments"

-- | Coerce the result type of an 'AppResult'.
--   The parameter @from_type@ must be the same as the return type of
--   @app_result@, and it must be coercible to @to_type@.
resultOfCoercion :: Type -> Type -> AppResult -> AppResult
resultOfCoercion from_type to_type app_result =
  app_result { appliedExpr = coerce $ appliedExpr app_result
             , appliedReturnType = to_type}
  where
    coerce mk_expr args = do
      expr <- mk_expr args
      coerceExpToReturnType from_type to_type expr

-- | Apply a type to an 'AppResult', producing a new 'AppResult'.
--   Applying to @arg_type@ must produce a result with type @result_type@.
--   Type correctness is not verified.
resultOfTypeApp :: Type -> Type -> AppResult -> AppResult
resultOfTypeApp result_type type_arg app_result =
  app_result { appliedExpr = app $ appliedExpr app_result
             , appliedReturnType = result_type}
  where
    app mk_expr args = do
      expr <- mk_expr args
      return $! apply_type expr
      where
        -- Incorporate the type argument into an existing application term,
        -- if possible
        apply_type :: ExpM -> ExpM
        apply_type (ExpM (AppE inf op ty_args [])) =
          ExpM $ AppE inf op (ty_args ++ [TypM type_arg]) []
        
        apply_type e =
          ExpM $ AppE defaultExpInfo e [TypM type_arg] []

resultOfApp :: Type -> Coercion -> AppResult -> AppResult
resultOfApp result_type co app_result =
  app_result { appliedExpr = app $ appliedExpr app_result
             , appliedCoercions = co : appliedCoercions app_result
             , appliedReturnType = result_type}
  where
    app mk_expr [] = internalError "resultOfApp: Wrong number of arguments"

    app mk_expr args = do
      let args' = init args
          arg   = last args
      expr <- mk_expr args'
      return $! apply_expr arg expr
      where
        -- Incorporate the argument into an existing application term, if
        -- possible
        apply_expr arg (ExpM (AppE inf op ty_args args)) =
          ExpM (AppE inf op ty_args (args ++ [arg]))

        apply_expr arg e =
          ExpM (AppE defaultExpInfo e [] [arg])

applyResultToValues :: AppResult -> [ExpM] -> RI (ExpM, Type)
applyResultToValues app_result arguments =
  let coercions = reverse $ appliedCoercions app_result
  in coerceExps coercions arguments $ \co_arguments -> do
    expr <- appliedExpr app_result co_arguments
    return (expr, appliedReturnType app_result)

-- | Compute the type of an application.  Coerce the type arguments, and 
--   return the coercions that should be applied to value arguments.
reprTypeOfApp :: ExpM           -- ^ Operator
              -> Type           -- ^ Operator type
              -> [TypeArgument] -- ^ Type arguments
              -> [Type]         -- ^ Types of value arguments
              -> RI AppResult
reprTypeOfApp op op_type ty_args arg_types = do
  instantiated_result <- foldM applyToTypeArg (appResult op op_type) ty_args
  foldM applyToArg instantiated_result arg_types

reprApply :: ExpM               -- ^ Operator
          -> Type               -- ^ Operator type
          -> [TypeArgument]     -- ^ Type arguments
          -> [(ExpM, Type)]     -- ^ Arguments and their types
          -> RI (ExpM, Type) -- ^ Computes the expression and return type
reprApply op op_type ty_args args = do
  app_result <- reprTypeOfApp op op_type ty_args (map snd args)
  applyResultToValues app_result (map fst args)

-- | Compute the result of a type application.
--   The operator and argument are coerced as needed, then applied.
applyToTypeArg :: AppResult -> (Type, Kind) -> RI AppResult
applyToTypeArg operator (arg_t, g_kind) =
  case appliedReturnType operator
  of AllT (a ::: e_kind) rng -> do
       -- Coerce the type argument to the correct kind
       coerced_type <- coerceType g_kind e_kind arg_t

       -- Compute the result of type application
       rng' <- substitute (singletonSubstitution a coerced_type) rng
       return $! resultOfTypeApp rng' coerced_type operator
     _ -> do
       -- Can we coerce the operator to the proper representation?
       tenv <- getTypeEnv
       op_type <- reduceToWhnf (appliedReturnType operator)
       co_op_type <- stripReprConversions op_type
       case co_op_type of
         AllT {} ->
           -- Coerce operator, then apply
           let operator' = resultOfCoercion op_type co_op_type operator
           in applyToTypeArg operator' (arg_t, g_kind)
         _ -> internalError "applyToTypeArg: Type error"

-- | Compute the result of an application, given the type of
--   the argument.
applyToArg :: AppResult -> Type -> RI AppResult
applyToArg operator arg_type =
  case appliedReturnType operator
  of FunT expected_type rng -> do
       arg_coercion <- coercion arg_type expected_type
       return $! resultOfApp rng arg_coercion operator
     _ -> do
       -- Can we coerce the operator to the proper representation?
       tenv <- getTypeEnv
       op_type <- reduceToWhnf (appliedReturnType operator)
       co_op_type <- stripReprConversions op_type
       case co_op_type of
         FunT {} ->
           -- Coerce operator, then apply
           let operator' = resultOfCoercion op_type co_op_type operator
           in applyToArg operator' arg_type
         _ -> internalError "applyToArg: Type error"

-------------------------------------------------------------------------------
-- Conversion of IR data structures

reprTyPat :: TyPat SF -> (TyPatM -> RI a) -> RI a
reprTyPat (TyPatSF (v ::: kind)) k =
  let kind' = cvtKind kind
  in assumeTypeKinds v kind kind' $ k (TyPatM (v ::: kind'))

reprLocalPat :: PatSF -> (PatM -> RI a) -> RI a
reprLocalPat (VarP v t) k = do
  (t', _) <- cvtNormalizeLocalType t
  assumeValueTypes v t t' $ k (memVarP (v ::: t'))

reprParam :: PatSF -> (PatM -> RI a) -> RI a
reprParam (VarP v t) k = do
  (t', _) <- cvtNormalizeParamType t
  assumeReprDict v t' $ assumeValueTypes v t t' $ k (memVarP (v ::: t'))

reprRet :: TypSF -> RI TypM
reprRet (TypSF t) = fmap (TypM . fst) $ cvtNormalizeReturnType t

-- | Convert an expression's representation
reprExp :: ExpSF -> RI (ExpM, Type)
reprExp expression = traceShow (text "reprExp" <+> pprExp expression) $
  case fromExpSF expression
  of VarE inf v -> do
       v_type <- riLookupType v
       return (ExpM (VarE inf v), v_type)
     LitE inf l -> return (ExpM (LitE inf l), literalType l)
     AppE inf op ty_args args ->
       reprApp inf op ty_args args
     LamE inf f -> do
       f' <- reprFun f
       let ret_type = TypecheckMem.functionType f'
       return (ExpM $ LamE inf f', ret_type)
     LetE inf pat rhs body -> do
       (rhs', rhs_type) <- reprExp rhs
       reprLocalPat pat $ \pat' -> do
         -- Coerce RHS to the expected type for this pattern
         let pat_type = patMType pat'
         coerceExpAtType rhs_type pat_type rhs' $ \rhs'' -> do

           -- Convert the body
           (body', body_type) <- reprExp body
           return (ExpM $ LetE inf pat' rhs'' body', body_type)
     LetfunE inf defs body ->
       withDefs defs $ \defs' -> do
         (body', body_type) <- reprExp body
         return (ExpM $ LetfunE inf defs' body', body_type)
     CaseE inf scr alts -> do 
       (scr', scr_type) <- reprExp scr
       -- TODO: coerce scrutinee
       
       -- Convert case alternatives.  Coerce them all to the same return type.
       (return_type, _) <- cvtNormalizeReturnType =<< riInferExpType expression
       alts' <- mapM (reprAlt return_type) alts
       return (ExpM $ CaseE inf scr' alts', return_type)
     ExceptE inf t -> do
       (t', _) <- cvtNormalizeNaturalType t
       return (ExpM $ ExceptE inf t', t')

reprApp inf op ty_args args = do
  (op', op_type) <- reprExp op
  repr_ty_args <- mapM (cvtNormalizeCanonicalType . fromTypSF) ty_args
  args' <- mapM reprExp args

  -- Compute result type and coerce arguments
  reprApply op' op_type repr_ty_args args'

-- | Convert a case alternative's representation, using the given type as
--   the return type.
reprAlt :: Type -> AltSF -> RI AltM
reprAlt return_type (AltSF alt) = do
  con_type <- riLookupDataCon (altConstructor alt)

  -- Convert type arguments and coerce to match the data type
  let ty_arg_kinds = [k | _ ::: k <- dataConPatternParams con_type]
  ty_args <- zipWithM convert_type_argument ty_arg_kinds (altTyArgs alt)

  -- Get kinds of existential types
  let ex_vars = [a | TyPatSF (a ::: _) <- altExTypes alt]
      sf_ex_types = [t | TyPatSF (_ ::: t) <- altExTypes alt]
  (ex_types, arg_types, _) <- instantiateDataConType con_type ty_args ex_vars

  let params = [x ::: t
               | (VarP x _, t) <- zip (altParams alt) arg_types]
      sf_param_types = [t | VarP _ t <- altParams alt]
  assume_ex_types sf_ex_types ex_types $
    assume_params sf_param_types params $ do
      (body, body_type) <- reprExp (altBody alt)
      
      -- Coerce the body's result
      co_body <- coerceExpToReturnType body_type return_type body

      return $ AltM $ Alt { altConstructor = altConstructor alt
                          , altTyArgs = map TypM ty_args
                          , altExTypes = map TyPatM ex_types
                          , altParams = map memVarP params
                          , altBody = co_body}
  where
    -- Convert a System F type to the expected type
    convert_type_argument expected_kind original_type = do
      (ty, kind) <- cvtNormalizeCanonicalType $ fromTypSF original_type
      coerceType kind expected_kind ty
      
    -- Add existential types to the type environments
    assume_ex_types sf_types binders m =
      foldr assume_type m (zip sf_types binders)
      where
        assume_type (sf_type, a ::: spec_type) m =
          assumeTypeKinds a sf_type spec_type m
    
    assume_params sf_types ps m =
      foldr assume_param m (zip sf_types ps)
      where
        assume_param (sf_type, v ::: spec_type) m =
          assumeValueTypes v sf_type spec_type m 

reprFun :: FunSF -> RI FunM
reprFun (FunSF f) =
  withMany reprTyPat (funTyParams f) $ \ty_params ->
  withMany reprParam (funParams f) $ \params -> do
    (body, body_type) <- reprExp (funBody f)
    ret <- reprRet (funReturn f)
    
    -- Coerce body to match the return type
    co_body <- coerceExpToReturnType body_type (fromTypM ret) body
    
    return $ FunM (Fun { funInfo = funInfo f
                       , funTyParams = ty_params
                       , funParams = params
                       , funReturn = ret
                       , funBody = co_body})

withDefs :: DefGroup (Def SF) -> (DefGroup (Def Mem) -> RI a) -> RI a
withDefs (NonRec def) k = do
  def' <- traceShow (pprDef def) $ mapMDefiniens reprFun def
  let sf_def_type = TypecheckSF.functionType $ definiens def
      def_type = TypecheckMem.functionType $ definiens def'
  assumeValueTypes (definiendum def') sf_def_type def_type $ k (NonRec def')

withDefs (Rec defs) k = assume_functions defs $ do
    defs' <- mapM (mapMDefiniens reprFun) defs
    k (Rec defs')
  where
    assume_functions (def : defs) m = do
      -- Compute the System F and specification types
      let fun_name = definiendum def
          sf_type = TypecheckSF.functionType $ definiens def
      (spec_type, _) <- cvtNormalizeNaturalType sf_type

      -- Add to type environment
      assumeValueTypes fun_name sf_type spec_type $ assume_functions defs m

    assume_functions [] m = m

reprExport e = do
  f <- reprFun $ exportFunction e
  return $ Export { exportSourcePos = exportSourcePos e 
                  , exportSpec = exportSpec e
                  , exportFunction = f}

reprTopLevelDefs :: [DefGroup (Def SF)]
                 -> [Export SF]
                 -> RI ([DefGroup (Def Mem)], [Export Mem])
reprTopLevelDefs defgroups exports = go id defgroups
  where
    go hd (g:gs) = withDefs g $ \g' -> go (hd . (g':)) gs
    go hd [] = do es <- mapM reprExport exports
                  return (hd [], es)

reprModule :: Module SF -> RI (Module Mem)
reprModule (Module mod_name defs exports) = do
  (defs', exports') <- reprTopLevelDefs defs exports
  return (Module mod_name defs' exports')

-- | Perform representation inference.
--
--   The specification type environment is used for representation inference.
representationInference :: Module SF -> IO (Module Mem)
representationInference mod = do
  withTheNewVarIdentSupply $ \supply -> do
    sf_type_env <- readInitGlobalVarIO the_systemFTypes
    type_env <- readInitGlobalVarIO the_specTypes
    (dict_env, int_env) <- runFreshVarM supply createDictEnv
    let context = RIEnv supply type_env dict_env int_env sf_type_env
    runReaderT (unRI (reprModule mod)) context
