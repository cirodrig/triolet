{-| Infer data structure representations.

The input program uses the pure type system.  All values are boxed
and have kind @box@.  The output program uses the specification type
system, in which values inhabit four different kinds: @val@, @box@,
@bare@, and @write@.

-}

{-# LANGUAGE FlexibleInstances, Rank2Types, GeneralizedNewtypeDeriving #-}
module SystemF.ReprInference(representationInference)
where

import Control.Applicative
import Control.Monad.Reader
import Data.Maybe
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
import qualified Type.Substitute as Substitute
import Type.Substitute(substitute)
import Type.Type
import SystemF.SpecToMem
import SystemF.EtaReduce
import SystemF.ReprDict
import SystemF.Syntax
import SystemF.Print
import SystemF.MemoryIR
import qualified SystemF.PrintMemoryIR as PrintMemoryIR
import qualified SystemF.TypecheckSF as TypecheckSF
import qualified SystemF.TypecheckMem as TypecheckMem

import Globals
import GlobalVar

-- Set to 'True' to print lots of debugging information
debugVerbose = False

whenDebug = when debugVerbose

printWhenDebug = whenDebug . print

-- | Check whether the @OutPtr@ or @Store@ constructors appear in a type.
--   The constructors should never be seen.  This function is for debugging.
checkForOutPtr :: Type -> Bool
checkForOutPtr (VarT t)
  | t == outPtrV = True
  | t == storeV = True
  | otherwise = False
checkForOutPtr (AppT op arg) =
  checkForOutPtr op || checkForOutPtr arg
checkForOutPtr (FunT dom rng) =
  checkForOutPtr dom || checkForOutPtr rng
checkForOutPtr (AllT (_ ::: dom) rng) =
  checkForOutPtr dom || checkForOutPtr rng
checkForOutPtr (LamT (_ ::: dom) body) =
  checkForOutPtr dom || checkForOutPtr body
checkForOutPtr (AnyT _) = False
checkForOutPtr (IntT _) = False
checkForOutPtr (UTupleT _) = False

-- | Report an error if 'checkForOutPtr' returns 'True'.
errorIfOutPtr :: Doc -> Type -> a -> a
errorIfOutPtr msg ty x
  | checkForOutPtr ty = internalError (show (msg <+> pprType ty))
  | otherwise = x

-- | The representation inference monad.
--
--   Specification types are tracked for variables that are in scope.
--   New variables can be created.
newtype RI a = RI {unRI :: ReaderT RIEnv IO a}
             deriving(Functor, Applicative, Monad, MonadIO)

-- | A first-order type rewrite rule.  When the type on the left is matched,
--   rewrite it to the type on the right.
data TypeRewrite = TR {trKind :: !Kind, trLHS :: Type, trRHS :: Type}

pprTypeRewrite :: TypeRewrite -> Doc
pprTypeRewrite (TR _ lhs rhs) =
  pprType lhs <+> text "=>" <+> pprType rhs

pprTypeRewrites xs = vcat $ map pprTypeRewrite xs

data RIEnv =
  RIEnv
  { riVarSupply :: {-#UNPACK#-}!(IdentSupply Var)

    -- | The specification type environment
  , riTypeEnv :: TypeEnv
  , riDictEnv :: SingletonValueEnv

    -- | Rewrite rules on the specification type environment.
    --   Each time a coercion is inserted into the type environment, the 
    --   corresponding rewrite rule is inserted here.
  , riRewrites :: [TypeRewrite]

    -- | The system F type environment
  , riSystemFTypeEnv :: BoxedTypeEnv
  }

instance Supplies RI (Ident Var) where
  fresh = RI $ ReaderT $ \env -> supplyValue (riVarSupply env)

instance TypeEnvMonad RI where
  type EvalBoxingMode RI = UnboxedMode
  getTypeEnv = RI $ asks riTypeEnv
  assumeWithProperties v t b m = RI $ local insert_type (unRI m)
    where
      insert_type env =
        env {riTypeEnv = insertTypeWithProperties v t b $ riTypeEnv env}

instance ReprDictMonad RI where
  getVarIDs = RI $ asks riVarSupply
  getDictEnv = RI $ asks riDictEnv
  localDictEnv f (RI m) = RI $ local f_dict m
    where
      f_dict env = env {riDictEnv = f $ riDictEnv env}

instance EvalMonad RI where
  liftTypeEvalM m = RI $ ReaderT $ \env -> do
    runTypeEvalM m (riVarSupply env) (riTypeEnv env)

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

getRewrites :: RI [TypeRewrite]
getRewrites = RI $ asks riRewrites

-- | Add a type to the System F type environment.
--
--   If it's a coercion type, add it to the set of rewrite rules too.
assumeSFType :: Var -> Type -> RI a -> RI a
assumeSFType v t m = RI $ local insert_type (unRI m)
  where
    insert_type env =
      env {riSystemFTypeEnv = insertType v t $ riSystemFTypeEnv env}

-- | For each coercion parameter inserted by type inference, add
--   a rewrite rule to the environment.  Each time a function parameter is
--   encountered, this function is called with the parameter's specification
--   type.  Types are ignored if they're not coercion types.
--   One rewrite rule is added for boxed types, another for bare types.
assumeCoercionType :: Type -> RI a -> RI a    
assumeCoercionType ty m = 
  case fromTypeApp ty
  of (CoT k, [s, t]) -> insert_rewrites k s t
     _ -> m
  where
    insert_rewrites k s t = do
      (rw_box, rw_bare) <- liftTypeEvalM $ create_rewrites k s t
      RI $ local (\env -> env {riRewrites = rw_box : rw_bare : riRewrites env}) (unRI m)

    create_rewrites (VarT k) s t
      | k == boxV =
          return (TR boxT s t, TR bareT (bareType s) (bareType t))
      | otherwise =
          internalError "assumeCoercionType: Not implemented for this kind"

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
-- Applying type rewrites

-- | Normalize a specification type by applying type coercions exhaustively.
--   Return the normalized type, and 'True' if any type coercions were applied.
normalizeSpecificationType :: Type -> RI (Bool, Type)
normalizeSpecificationType ty = RI $ ReaderT $ \env ->
  let apply_coercions = applyTypeCoercionsExhaustively (riRewrites env) ty
  in runTypeEvalM apply_coercions (riVarSupply env) (riTypeEnv env)

-- | Apply a type coercion to a type, if its LHS exactly matches.
applyTypeCoercion :: TypeRewrite -> Kind -> Type -> UnboxedTypeEvalM (Bool, Type)
applyTypeCoercion (TR rewrite_kind lhs rhs) ty_kind ty = do
  -- We can only compare the types if they have the same kind
  same_kind <- compareTypes rewrite_kind ty_kind
  if same_kind then try_apply else return (False, ty)
  where
    try_apply = do
      eq <- compareTypes lhs ty
      return $! if eq then trace_rewrite (True, rhs) else (False, ty)
    trace_rewrite = id
    -- trace_rewrite = traceShow (text "Rewrite" <+> pprType lhs <+> text "==>" <+> pprType rhs)

-- | Apply any matching type coercion to a type.
applyTypeCoercions :: [TypeRewrite] -> Type -> UnboxedTypeEvalM (Bool, Type)
applyTypeCoercions rws ty = do
  tenv <- getTypeEnv
  let kind = typeKind tenv ty

  let loop (rw:rws) = applyTypeCoercion rw kind ty >>= continue
        where
          continue new@(True, _) = return new
          continue (False, _)    = loop rws
      loop [] = return (False, ty)

  loop rws

-- | Apply any matching type coercion to a type or any subexpression.
applyTypeCoercionsRec :: [TypeRewrite] -> Type -> UnboxedTypeEvalM (Bool, Type)
applyTypeCoercionsRec rws ty = do
  -- Rewrite this expression
  whnf_ty <- reduceToWhnf ty
  (progress, ty') <- applyTypeCoercions rws whnf_ty
  let no_change = return (progress, ty')

  -- Rewrite subexpressions
  ty'' <- Substitute.freshen ty'
  case ty'' of
    VarT _      -> no_change
    AppT t1 t2  -> recurse progress AppT t1 t2
    FunT t1 t2  -> recurse progress FunT t1 t2
    LamT b body -> bind progress LamT b body
    AllT b body -> bind progress AllT b body
    IntT _      -> no_change
    CoT _       -> no_change
    UTupleT _   -> no_change
  where
    recurse progress con t1 t2 = do 
      (progress1, t1') <- applyTypeCoercionsRec rws t1
      (progress2, t2') <- applyTypeCoercionsRec rws t2
      let p = progress || progress1 || progress2
      p `seq` return (p, con t1' t2')

    bind progress con binder body = do
      (progress1, body') <-
        assumeBinder binder $ applyTypeCoercionsRec rws body
      let p = progress || progress1
      p `seq` return (p, con binder body')

-- | Apply type coercions until no further rewriting is possible.
applyTypeCoercionsExhaustively :: [TypeRewrite] -> Type
                               -> UnboxedTypeEvalM (Bool, Type)
applyTypeCoercionsExhaustively rws ty = do
  -- liftIO $ print $
  --   hang (text "Type coercions" <+> pprType ty) 4 (pprTypeRewrites rws)
  loop False ty
  where
    loop change ty = do 
      (change', ty') <- applyTypeCoercionsRec rws ty
      if change'
        then loop True ty'
        else return (change, ty')

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
           | isAdapterCon op -> strip True arg
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
           Just $! dataTypeKind dtype
       | Just _ <- lookupTypeFunction op tenv ->
           -- Use the type function's return kind
           Just $! toBaseKind $ typeKind tenv natural_t
       | otherwise -> Nothing
     Nothing ->
       case natural_t
       of FunT {} -> Just BoxK
          AllT {} -> Just BoxK
          AppT (AppT (CoT (VarT co_kind)) _) _ 
            | co_kind == boxV -> Just ValK
          _ -> internalError "coercionKind: Not implemented for this type"

-- | Given two types returned by 'stripReprConversions',
--   determine the natural kind of the most specific head type.
--
--   If both types have variables or functions as their outermost term, 
--   then Nothing is returned.
mostSpecificNaturalHeadKind :: (EvalMonad m, EvalBoxingMode m ~ UnboxedMode) =>
                               Type -> Type -> m BaseKind
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
           of Just (op, [arg]) | op `isCoreBuiltin` The_Stored -> return arg
              _ -> internalError "coerceType"
       | e_kv == valV && g_kv == boxV ->
           case fromVarApp g_t
           of Just (op, [arg]) | op `isCoreBuiltin` The_AsBox ->
                case fromVarApp arg
                of Just (op, [arg2]) | op `isCoreBuiltin` The_Stored -> return arg2
                   _ -> internalError "coerceType"
              _ -> internalError "coerceType"
       | e_kv == boxV && g_kv == valV ->
           return $
           varApp (coreBuiltin The_AsBox)
           [varApp (coreBuiltin The_Stored) [g_t]]
       | e_kv == boxV && g_kv == bareV ->
           return $ boxedType g_t
       | e_kv == bareV && g_kv == valV ->
           return $varApp (coreBuiltin The_Stored) [g_t]
       | e_kv == bareV && g_kv == boxV ->
           return $ bareType g_t
     (e_dom `FunT` e_rng, g_dom `FunT` g_rng)
       | sameKind e_dom g_dom && sameKind e_rng g_rng ->
           return g_t -- No need to coerce
       | otherwise -> do
           param <- newAnonymousVar TypeLevel
           assume param e_dom $ do
             coerced_param <- coerceType e_dom g_dom (VarT param)
             coerced_result <- coerceType g_rng e_rng $ AppT g_t coerced_param
             return $ LamT (param ::: e_dom) coerced_result
     _ -> internalError $ "coerceType: Cannot coerce " ++ show (pprType g_k) ++ " to " ++ show (pprType e_k)

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
writeType t = varApp initConV [t]
boxedType t = varApp (coreBuiltin The_AsBox) [t]
bareType t  = varApp (coreBuiltin The_AsBare) [t]

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

cvtType mode (CoT (VarT k)) 
  | k == boxV = do
    -- Coercion type
    -- Always generate coercions on boxed objects.
    return (CoT (VarT k), boxT `FunT` boxT `FunT` valT)

cvtType mode (CoT _) =
  internalError "cvtType: Unexpected kind in coercion type"

cvtType mode ty@(IntT n) = return (ty, intindexT)

-- | Convert a System F type to its natural representation.
--   Try to simplify the resulting type expression.
cvtNormalizeNaturalType :: Type -> RI (Type, Kind)
cvtNormalizeNaturalType t = do
  (t', k) <- cvtNaturalType t
  t'' <- normalize t'
  liftIO $ printWhenDebug $ text "Convert NT" <+> (pprType t $$ pprType t'')
  return (t'', k)

-- | Convert a System F type to its canonical representation.
--   Try to simplify the resulting type expression.
cvtNormalizeCanonicalType :: Type -> RI (Type, Kind)
cvtNormalizeCanonicalType t = do
  (t', k) <- cvtCanonicalType t
  t'' <- normalize t'
  liftIO $ printWhenDebug $ text "Convert CT" <+> (pprType t $$ pprType t'')
  return (t'', k)

-- | Convert a System F type to the preferred representation for a 
--   local variable.
--   Try to simplify the resulting type expression.
cvtNormalizeLocalType :: Type -> RI (Type, Kind)
cvtNormalizeLocalType t = do
  (t', k) <- cvtLocalType t
  t'' <- normalize t'
  liftIO $ printWhenDebug $ text "Convert LT" <+> (pprType t $$ pprType t'')
  return (t'', k)

-- | Convert a System F type to the preferred representation for a 
--   function parameter.
--   Try to simplify the resulting type expression.
cvtNormalizeParamType :: Type -> RI (Type, Kind)
cvtNormalizeParamType t = do
  (t', k) <- cvtParamType t
  t'' <- normalize t'
  liftIO $ printWhenDebug $ text "Convert PT" <+> (pprType t $$ pprType t'')
  return (t'', k)

-- | Convert a System F type to the preferred representation for a 
--   function return.
--   Try to simplify the resulting type expression.
cvtNormalizeReturnType :: Type -> RI (Type, Kind)
cvtNormalizeReturnType t = do
  (t', k) <- cvtReturnType t
  t'' <- normalize t'
  liftIO $ printWhenDebug $ text "Convert RT" <+> (pprType t $$ pprType t'')
  return (t'', k)

-------------------------------------------------------------------------------
-- Coercing expressions

-- | A coercion.  Given an expression and a continuation that uses the
--   coerced expression to create a new expression, create an application of
--   the continuation to the coerced expression.
--
--   Coercions may wrap the producer of the coerced value (the expression)
--   with additional code.
--
--   It used to be the case that coercions could wrap the consumer of the
--   coerced value (the continuation's result), which is why we take a
--   continuation argument.  We no longer do that, though.  It would be
--   possible to simplify this data type.
--
--   TODO: Change the data constructor to
--   > Coercion !(ExpM -> RI ExpM)
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
toStoredCoercion ty = Coercion $ \k e ->
  k (ExpM $ ConE defaultExpInfo stored_con [e])
  where
    stored_con = VarCon (coreBuiltin The_stored) [ty] []

-- | Coerce @bare -> val@ using the @stored@ constructor.
--   The argument is the @val@ type.
fromStoredCoercion :: Type -> Coercion
fromStoredCoercion ty = Coercion $ \k e -> do
  val_var <- newAnonymousVar ObjectLevel
  let decon = VarDeCon (coreBuiltin The_stored) [ty] []
  let alt = AltM $ Alt { altCon = decon
                       , altParams = [patM (val_var ::: ty)]
                       , altBody = ExpM $ VarE defaultExpInfo val_var}
      cas = ExpM $ CaseE defaultExpInfo e [alt]
  k cas

-- | Coerce @writer -> box@ using the @asbox@ function.
--   The argument is the @bare@ type.
toBoxedTypeCoercion :: Type -> Coercion
toBoxedTypeCoercion ty = Coercion $ \k e -> do
  dict <- withReprDict ty return
  k (ExpM $ AppE defaultExpInfo box_op [ty] [dict, e])
  where
    box_op = ExpM $ VarE defaultExpInfo (coreBuiltin The_asbox)

-- | Coerce @box -> writer@ using the @asbare@ function.
--   The argument is the @bare@ type.
toBareTypeCoercion :: Type -> Coercion
toBareTypeCoercion ty = Coercion $ \k e -> do
  dict <- withReprDict ty return
  k (ExpM $ AppE defaultExpInfo bare_op [ty] [dict, e])
  where
    bare_op = ExpM $ VarE defaultExpInfo (coreBuiltin The_asbare)

-- | Coerce @read -> write@ using the @copy@ function.
--   The argument is the @bare@ type.
copyCoercion :: Type -> Coercion
copyCoercion ty = Coercion $ \k e -> do
  dict <- withReprDict ty return
  k (ExpM $ AppE defaultExpInfo copy_op [ty] [dict, e])
  where
    copy_op = ExpM $ VarE defaultExpInfo (coreBuiltin The_copy)

-- | Coerce @write -> bare@ by assigning to a temporary variable, then
--   reading from the temporary variable.
--   The argument is the @bare@ type.
--    
--   Note that the data is put into a box, /not/ converted to a boxed 
--   representation.

-- The generated code is:
-- k (case Boxed e of Boxed read_var. read_var)
writeLocalCoercion :: Type -> Coercion
writeLocalCoercion ty = Coercion $ \k e -> do
  read_var <- newAnonymousVar ObjectLevel
  let rhs = ExpM $ ConE defaultExpInfo box_con [e]
      expr_alt = AltM $ Alt { altCon = box_decon
                            , altParams = [patM (read_var ::: ty)]
                            , altBody = ExpM $ VarE defaultExpInfo read_var}
      body = ExpM $ CaseE defaultExpInfo rhs [expr_alt]
  k body
  where
    box_con = VarCon (coreBuiltin The_boxed) [ty] []
    box_decon = VarDeCon (coreBuiltin The_boxed) [ty] []
    box_type = varApp (coreBuiltin The_Boxed) [ty]

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
      traceShow (pprType (forallType e_tydom $ funType e_dom e_rng) $$
                 pprType (forallType g_tydom $ funType g_dom g_rng)) $
      internalError "functionCoercion: Mismached function types"
  | null g_dom =
      internalError "functionCoercion: Not a function type"
  | otherwise = Coercion $ \k given_e -> make_wrapper_function given_e >>= k
  where
    make_wrapper_function given_e = do
      -- Insert expected function types into environment
      assume_ty_params $ withMany define_param e_dom $ \e_params -> do

        -- Compute result type and coerce arguments
        let given_type = forallType g_tydom (funType g_dom g_rng)
          
        -- Expected parameters will be passed as type arguments
        let type_args = [(VarT a, k) | a ::: k <- e_tydom]
            value_args = [(ExpM $ VarE defaultExpInfo (patMVar p),
                           patMType p)
                         | p <- e_params]

        -- Create a call to the original function
        (call, return_type) <-
          reprApply given_e given_type type_args value_args
        body <- coerceExpToReturnType return_type e_rng call

        -- Create a lambda function
        let fun_ty_args = [TyPat d | d <- e_tydom]
            fun_ret = e_rng
            fun =
              FunM $ Fun defaultExpInfo fun_ty_args e_params fun_ret body
        return $ ExpM $ LamE defaultExpInfo fun

    -- Add the expected function type parameters to the environment
    assume_ty_params m = foldr assumeBinder m e_tydom

    -- Define a pattern for a value parameter
    define_param ty k = do
      v <- newAnonymousVar ObjectLevel
      assume v ty $ k (patM (v ::: ty))

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

-- | Create a coercion that coerces a value from the given specification
--   type to the expected specification type.
coercion :: [TypeRewrite]
         -> Type                -- ^ Given type
         -> Type                -- ^ Expected type
         -> UnboxedTypeEvalM Coercion  -- ^ Computes the coercion
coercion rewrites g_type e_type = do
  tenv <- getTypeEnv

  -- Apply type coercions so that the types are normalized
  (coerce_g_type, normalized_g_type) <-
    applyTypeCoercionsExhaustively rewrites g_type
  (coerce_e_type, normalized_e_type) <-
    applyTypeCoercionsExhaustively rewrites e_type

  -- Get the kinds 
  whnf_g_type <- reduceToWhnf normalized_g_type
  whnf_e_type <- reduceToWhnf normalized_e_type
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

    liftIO $ printWhenDebug $ text "Coerce " <+>
      (pprType g_type $$
       text "to" <+> pprType e_type $$
       text "via" <+> text (show coerce_kind) $$
       text (show g_kind) <+> text (show e_kind))
  
    -- Create a coercion.  Coerce to the natural representation,
    -- then coerce the value, then coerce to the output representation.
    let co0 = if coerce_g_type 
              then typeCoercion g_type normalized_g_type g_kind
              else IdCoercion
    co1 <- representationCoercion natural_g_type coerce_kind g_kind coerce_kind
    co2 <- valueCoercion coerce_kind natural_g_type natural_e_type
    co3 <- representationCoercion natural_e_type coerce_kind coerce_kind e_kind
    let co4 = if coerce_e_type
              then typeCoercion normalized_e_type e_type e_kind
              else IdCoercion
    return (co4 `mappend` co3 `mappend` co2 `mappend` co1 `mappend` co0)

typeCoercion from_type to_type kind = Coercion $ \k e ->
  k (ExpM $ CoerceE defaultExpInfo from_type to_type e)

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
     (BareK, BoxK)        -> coerce_via WriteK
     (BareK, WriteK)      -> return $ copyCoercion bare_ty
     (WriteK, ValK)       -> coerce_via BareK
     (WriteK, BoxK)       -> return $ toBoxedTypeCoercion bare_ty
     (WriteK, BareK)      -> return $ writeLocalCoercion bare_ty
     _                    -> invalid_coercion
  where
    invalid_coercion =
      internalError $ "Attempt to generate invalid coercion: " ++
      show g_kind ++ " -> " ++ show e_kind

    -- The bare object type corresponding to natural_ty
    bare_ty =
      case natural_kind
      of ValK  -> varApp (coreBuiltin The_Stored) [natural_ty]
         BareK -> natural_ty
         BoxK  -> bareType natural_ty

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
       else traceShow (text "valueCoercion" <+> (pprType g_type $$ pprType e_type)) $
            internalError "valueCoercion: Not implemented for this type"

coerceExpAtType :: Type -> Type -> ExpM -> (ExpM -> RI (ExpM, a))
                -> RI (ExpM, a)
coerceExpAtType g_type e_type e k = do
  rewrites <- getRewrites
  co <- liftTypeEvalM $ coercion rewrites g_type e_type
  coerceExp co e k
  where
    debug = traceShow $ text "coerceExpAtType" <+> PrintMemoryIR.pprExp e

-- | Coerce an expression and return the result.  This is only valid for
--   return types, because we can't put a case statement around the consumer
--   when using this coercion strategy.
coerceExpToReturnType :: Type -> Type -> ExpM -> RI ExpM
coerceExpToReturnType g_type e_type e =
  fmap fst $ coerceExpAtType g_type e_type e $ \e' -> return (e', ())

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
--
--   TODO: Get rid of this data structure.
--   We should just apply arguments and type arguments one by one, without
--   jumping through hoops.
data InfAppResult =
    -- | An application of a function or data constructor to arguments 
    FunAppResult
    { -- | The applied expression, except for value arguments which must be
      --   supplied separately.  The /coerced/ arguments will be passed to this
      --   function.
      appliedExpr            :: [ExpM] -> RI ExpM

      -- | The result of the applied expression
    , appliedReturnType      :: Type

      -- | Coercions that should be applied to value arguments
      --   (in reverse order, relative to arguments)
    , appliedCoercions       :: [Coercion]

      -- | For constructors, the number of value arguments that must be
      --   applied.  The number decreases toward zero as more arguments are
      --   applied.  The count does not include an output pointer count.
    , appliedArityRemaining  :: !(Maybe Int)
    }
    -- | A data constructor that requires type arguments.
    --   Currently, existential types are not supported.
    --
    --   A 'FunAppResult' is produced once all type arguments have
    --   been supplied.
  | VarConExpectingTypes
    { appliedConstructor     :: !Var
    , appliedTypeArgs        :: [Type]
    , appliedUnivArity       :: !Int -- ^ Number of universal type arguments
    , appliedConstructorType :: !DataConType
    , appliedReturnType      :: Type
    }

appResult :: ExpM -> Type -> InfAppResult
appResult e ty = FunAppResult { appliedExpr           = mk_expr
                              , appliedReturnType     = ty
                              , appliedCoercions      = []
                              , appliedArityRemaining = Nothing}
  where
    mk_expr [] = return e
    mk_expr _  = internalError "appResult: Wrong number of arguments"

conAppResult :: Var -> DataConType -> Type -> InfAppResult
conAppResult v data_type ty
  | num_args == 0 =
      -- No type parameters required
      FunAppResult { appliedExpr = mk_expr
                  , appliedReturnType = ty
                  , appliedCoercions = []
                  , appliedArityRemaining =
                      case dataConFieldTypes data_type
                      of [] -> Nothing
                         xs -> Just $ length xs
                  }
  | otherwise =
      VarConExpectingTypes { appliedConstructor = v
                           , appliedTypeArgs    = []
                           , appliedUnivArity = univ_arity
                           , appliedConstructorType = data_type
                           , appliedReturnType = ty}
  where
    univ_arity = length (dataConTyParams data_type)

    -- Number of type arguments expected by the constructor
    num_args = length (dataConExTypes data_type) + univ_arity

    -- Create a constructor term with no type arguments
    mk_expr [] = return $ conE defaultExpInfo (VarCon v [] []) []
    mk_expr _  = internalError "conAppResult: Wrong number of arguments"

-- | Coerce the result type of an 'InfAppResult'.
--   The parameter @from_type@ must be the same as the return type of
--   @app_result@, and it must be coercible to @to_type@.
resultOfCoercion :: Type -> Type -> InfAppResult -> InfAppResult
resultOfCoercion from_type to_type app_result =
  app_result { appliedExpr = coerce $ appliedExpr app_result
             , appliedReturnType = to_type
               -- Coercion never produces a partially applied constructor term
             , appliedArityRemaining = Nothing}
  where
    coerce mk_expr args = do
      expr <- mk_expr args

      -- Eta-expand the constructor if needed
      expr2 <- case appliedArityRemaining app_result
               of Nothing -> return expr
                  Just n  -> eta_expand n from_type expr
      coerceExpToReturnType from_type to_type expr
    
    -- Eta-expand the expression by @n@ arguments
    eta_expand n from_type expr = do
      param_vars <- replicateM n $ newAnonymousVar ObjectLevel
      let (param_types, result_type) = take_parameter_types n from_type
      
      let fun_params = map patM $ zipWith (:::) param_vars param_types
          new_args = [ExpM (VarE defaultExpInfo v) | v <- param_vars]
          fun_body = case expr
                     of ExpM (ConE inf con args) ->
                          ExpM (ConE inf con (args ++ new_args))
      let fun = FunM $ Fun { funInfo = defaultExpInfo
                           , funTyParams = []
                           , funParams = fun_params
                           , funReturn = result_type
                           , funBody = fun_body}
      return $ ExpM $ LamE defaultExpInfo fun
      where
        take_parameter_types n ty = go id n ty
          where
            go hd 0 ty = (hd [], ty)
            go hd n (FunT dom rng) = go (hd . (dom:)) (n-1) rng
            
            -- Should not happen in a well-typed program
            go _ _ _ = internalError "resultOfCoercion"

-- | Apply a type to an 'InfAppResult', producing a new 'InfAppResult'.
--   Applying to @arg_type@ must produce a result with type @result_type@.
--   Type correctness is not verified.
resultOfTypeApp :: Type -> Type -> InfAppResult -> InfAppResult
resultOfTypeApp result_type type_arg (FunAppResult base_exp _ co _) =
  FunAppResult (app base_exp) result_type co Nothing
  where
    app mk_expr args = do
      expr <- mk_expr args
      return $! apply_type expr
      where
        -- Incorporate the type argument into an existing application term,
        -- if possible
        apply_type :: ExpM -> ExpM
        apply_type (ExpM (AppE inf op ty_args [])) =
          ExpM $ AppE inf op (ty_args ++ [type_arg]) []
        
        apply_type e =
          ExpM $ AppE defaultExpInfo e [type_arg] []

resultOfTypeApp result_type type_arg (VarConExpectingTypes con ty_args univ_arity data_con _) =
  -- Does the result of type application have all type arguments?
  if 1 + length ty_args == num_ty_args
  then FunAppResult mk_expr result_type [] (Just num_fields)
  else VarConExpectingTypes con ty_args' univ_arity data_con result_type
  where
    num_ty_args = length (dataConTyParams data_con) +
                  length (dataConExTypes data_con)
    num_fields = length (dataConFieldTypes data_con)

    ty_args' = ty_args ++ [type_arg]

    mk_expr [] =
      let u_args = take (length (dataConTyParams data_con)) ty_args'
          e_args = drop (length (dataConTyParams data_con)) ty_args'
      in return $ conE defaultExpInfo (VarCon con u_args e_args) []
    mk_expr _  = internalError "resultOfTypeApp: Wrong number of arguments"

resultOfApp :: Type -> Coercion -> InfAppResult -> InfAppResult
resultOfApp _ _ (VarConExpectingTypes {}) = 
  internalError "resultOfApp: Expecting type arguments"

resultOfApp result_type co app_result =
  app_result { appliedExpr = app $ appliedExpr app_result
             , appliedCoercions = co : appliedCoercions app_result
             , appliedReturnType = result_type
             , appliedArityRemaining =
                 case appliedArityRemaining app_result
                 of Nothing -> Nothing
                    Just 1  -> Nothing 
                    Just n -> Just $! n - 1
             }
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

        -- Add to the existing term only if the constructor isn't saturated
        apply_expr arg (ExpM (ConE inf con args)) 
          | isJust $ appliedArityRemaining app_result =
              ExpM (ConE inf con (args ++ [arg]))

        apply_expr arg e =
          ExpM (AppE defaultExpInfo e [] [arg])

applyResultToValues :: InfAppResult -> [ExpM] -> RI (ExpM, Type)
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
              -> RI InfAppResult
reprTypeOfApp op op_type ty_args arg_types = do
  instantiated_result <- foldM applyToTypeArg (appResult op op_type) ty_args
  foldM applyToArg instantiated_result arg_types
  where
    debug x = traceShow (text "reprTypeOfApp" <+> PrintMemoryIR.pprExp op) x

reprApply :: ExpM               -- ^ Operator
          -> Type               -- ^ Operator type
          -> [TypeArgument]     -- ^ Type arguments
          -> [(ExpM, Type)]     -- ^ Arguments and their types
          -> RI (ExpM, Type) -- ^ Computes the expression and return type
reprApply op op_type ty_args args = do
  app_result <- reprTypeOfApp op op_type ty_args (map snd args)
  applyResultToValues app_result (map fst args)
  where
    debug x =
      traceShow (text "reprApply" <+>
                 vcat (parens (pprType op_type) :
                       PrintMemoryIR.pprExp op :
                       map (pprType . fst) ty_args ++
                       map (PrintMemoryIR.pprExp . fst) args)) x

reprApplyCon :: Var                -- ^ Constructor
             -> [TypeArgument]     -- ^ Type arguments
             -> [(ExpM, Type)]     -- ^ Arguments and their types
             -> RI (ExpM, Type) -- ^ Computes the expression and return type
reprApplyCon op ty_args args = do
  -- Set up data for use by 'applyToTypeArg'
  tenv <- getTypeEnv

  -- Compute type of this data 
  let Just (dtype, data_con) = lookupDataConWithType op tenv
      init_type t ValK  = t
      init_type t BoxK  = t
      init_type t BareK = writeType t
      arg_types = zipWith init_type
                  (dataConFieldTypes data_con)
                  (dataConFieldKinds data_con)
      ret_type = init_type
                 (varApp (dataTypeCon dtype) $
                  map (VarT . binderVar) (dataConTyParams data_con))
                 (dataTypeKind dtype)
      op_type = forallType (dataConTyParams data_con) $
                forallType (dataConExTypes data_con) $
                funType arg_types ret_type

  let constructor_app_result = conAppResult op data_con op_type
  
  -- Apply type arguments
  instantiated_result <- foldM applyToTypeArg constructor_app_result ty_args

  -- Apply values
  app_result <- foldM applyToArg instantiated_result (map snd args)
  applyResultToValues app_result (map fst args)

-- | Compute the result of a type application.
--   The operator and argument are coerced as needed, then applied.
applyToTypeArg :: InfAppResult -> (Type, Kind) -> RI InfAppResult
applyToTypeArg operator (arg_t, g_kind) =
  case appliedReturnType operator
  of AllT (a ::: e_kind) rng -> do
       -- Coerce the type argument to the correct kind
       coerced_type <- coerceType g_kind e_kind arg_t

       -- Compute the result of type application
       rng' <- substitute (Substitute.singleton a coerced_type) rng
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
applyToArg :: InfAppResult -> Type -> RI InfAppResult
applyToArg operator arg_type =
  case appliedReturnType operator
  of FunT expected_type rng -> do
       rewrites <- getRewrites
       arg_coercion <- liftTypeEvalM $ coercion rewrites arg_type expected_type
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

reprTyPat :: TyPat -> (TyPat -> RI a) -> RI a
reprTyPat (TyPat (v ::: kind)) k =
  let kind' = cvtKind kind
  in assumeTypeKinds v kind kind' $ k (TyPat (v ::: kind'))

reprLocalPat :: PatSF -> (PatM -> RI a) -> RI a
reprLocalPat (VarP v t) k = do
  (t', _) <- cvtNormalizeLocalType t
  assumeValueTypes v t t' $ k (patM (v ::: t'))

reprParam :: PatSF -> (PatM -> RI a) -> RI a
reprParam (VarP v t) k = do
  (t', _) <- cvtNormalizeParamType t
  let pattern = patM (v ::: t')
  saveReprDictPattern pattern $
    assumeCoercionType t' $
    assumeValueTypes v t t' $
    k pattern

reprRet :: Type -> RI Type
reprRet t = fmap fst $ cvtNormalizeReturnType t

-- | Convert an expression's representation.  Return its specification type.
reprExp :: ExpSF -> RI (ExpM, Type)
reprExp expression =
  case fromExpSF expression
  of VarE inf v -> do
       v_type <- riLookupType v
       return (ExpM (VarE inf v), v_type)
     LitE inf l -> return (ExpM (LitE inf l), literalType l)
     ConE inf op args ->
       reprCon inf op args
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
       withFDefs defs $ \defs' -> do
         (body', body_type) <- reprExp body
         return (ExpM $ LetfunE inf defs' body', body_type)
     CaseE inf scr alts -> reprCase expression inf scr alts
     ExceptE inf t -> do
       (t', _) <- cvtNormalizeNaturalType t
       return (ExpM $ ExceptE inf t', t')

     CoerceE inf from_t to_t body -> do
       -- The two types involved in the coercion may have different
       -- natural kinds.  Ensure that the types are converted to the _same_
       -- canonical kind.
       (body', body_type) <- reprExp body
       
       -- Determine the boxed form of from_t
       tenv <- getTypeEnv
       from_t' <- cvtCanonicalReturnType from_t 
       co_body <- coerceExpToReturnType body_type from_t' body'
       
       -- The new return type is the boxed version of to_t
       to_t' <- cvtCanonicalReturnType to_t
       return (ExpM $ CoerceE inf from_t' to_t' co_body, to_t')

     ArrayE inf ty exps -> do
       -- Convert the array element type to a bare type
       elt_ty <- do (ty', k) <- cvtCanonicalType ty
                    coerceType k bareT ty'

       -- Create the initializer type
       let write_elt_type = writeType elt_ty
       exps' <- mapM (reprArrayElt write_elt_type) exps

       -- Return an initializer type
       let len = IntT (fromIntegral $ length exps)
           ret_type = writeType $ typeApp arrT [len, elt_ty]
       return (ExpM $ ArrayE inf elt_ty exps', ret_type)

reprArrayElt elt_ty e = do
  -- Convert array element
  (e', t) <- reprExp e

  -- Coerce the expression
  coerceExpToReturnType t elt_ty e'

reprCon inf op args = do
  let VarCon con ty_args ex_args = op

  -- Compute representations of arguments
  repr_ty_args <- mapM cvtNormalizeCanonicalType ty_args
  repr_ex_args <- mapM cvtNormalizeCanonicalType ex_args
  args' <- mapM reprExp args
  
  -- Compute result type and coerce arguments
  reprApplyCon con (repr_ty_args ++ repr_ex_args) args'

reprApp inf op ty_args args = do
  (op', op_type) <- reprExp op
  repr_ty_args <- mapM cvtNormalizeCanonicalType ty_args
  args' <- mapM reprExp args

  -- Compute result type and coerce arguments
  reprApply op' op_type repr_ty_args args'

reprCase original_exp inf scr alts = do
  -- Produce a scrutinee in the natural representation
  (scr', scr_type) <- reprExp scr
  (natural_scr_type, _) <- cvtNormalizeNaturalType =<< riInferExpType scr
  coerceExpAtType scr_type natural_scr_type scr' $ \natural_scr -> do

    -- Convert case alternatives.  Coerce them all to the same return type.
    (return_type, _) <- cvtNormalizeReturnType =<< riInferExpType original_exp
    alts' <- mapM (reprAlt return_type) alts

    return (ExpM $ CaseE inf natural_scr alts', return_type)

-- | Convert a case alternative's representation, using the given type as
--   the return type.
reprAlt :: Type -> AltSF -> RI AltM
reprAlt return_type (AltSF alt) = do
  let VarDeCon op ty_args ex_types = altCon alt 
  con_type <- riLookupDataCon op

  -- Convert type arguments and coerce to match the data type
  let ty_arg_kinds = [k | _ ::: k <- dataConTyParams con_type]
  ty_args <- zipWithM convert_type_argument ty_arg_kinds ty_args

  -- Get kinds of existential types
  let ex_vars = [a | a ::: _ <- ex_types]
      sf_ex_types = [t | _ ::: t <- ex_types]
  (ex_types, arg_types, _) <- instantiateDataConType con_type ty_args ex_vars

  let params = [x ::: t
               | (VarP x _, t) <- zip (altParams alt) arg_types]
      sf_param_types = [t | VarP _ t <- altParams alt]
  assume_ex_types sf_ex_types ex_types $
    assume_params sf_param_types params $ do
      (body, body_type) <- reprExp (altBody alt)
      
      -- Coerce the body's result
      co_body <- coerceExpToReturnType body_type return_type body

      return $ AltM $ Alt { altCon = VarDeCon op ty_args ex_types
                          , altParams = map patM params
                          , altBody = co_body}
  where
    -- Convert a System F type to the expected type
    convert_type_argument expected_kind original_type = do
      (ty, kind) <- cvtNormalizeCanonicalType original_type
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
    co_body <- coerceExpToReturnType body_type ret body
    
    return $ FunM (Fun { funInfo = funInfo f
                       , funTyParams = ty_params
                       , funParams = params
                       , funReturn = ret
                       , funBody = co_body})

reprEnt :: Ent SF -> RI (Ent Mem)
reprEnt (FunEnt f) = FunEnt `liftM` reprFun f
reprEnt (DataEnt (Constant inf ty e)) = do
  (ty', _) <- cvtNormalizeLocalType ty
  (e', _) <- reprExp e
  return $ DataEnt $ Constant inf ty' e'

withDefs :: (t SF -> RI (t Mem))
         -> (t SF -> Type)
         -> (t Mem -> Type)
         -> DefGroup (Def t SF) -> (DefGroup (Def t Mem) -> RI a) -> RI a
withDefs convert_def get_sf_type get_mem_type (NonRec def) k = do
  def' <- mapMDefiniens convert_def def
  let sf_def_type = get_sf_type $ definiens def
      def_type = get_mem_type $ definiens def'
  assumeValueTypes (definiendum def') sf_def_type def_type $ k (NonRec def')

withDefs convert_def get_sf_type get_mem_type (Rec defs) k =
  assume_functions defs $ do
    defs' <- mapM (mapMDefiniens convert_def) defs
    k (Rec defs')
  where
    assume_functions (def : defs) m = do
      -- Compute the System F and specification types
      let fun_name = definiendum def
          sf_type = get_sf_type $ definiens def
      (spec_type, _) <- cvtNormalizeNaturalType sf_type

      -- Add to type environment
      assumeValueTypes fun_name sf_type spec_type $ assume_functions defs m

    assume_functions [] m = m

withFDefs = withDefs reprFun TypecheckSF.functionType TypecheckMem.functionType

withGDefs = withDefs reprEnt entity_type entityType
  where
    entity_type (FunEnt f) = TypecheckSF.functionType f
    entity_type (DataEnt d) = constType d

reprExport e = do
  f <- reprFun $ exportFunction e
  return $ Export { exportSourcePos = exportSourcePos e 
                  , exportSpec = exportSpec e
                  , exportFunction = f}

reprTopLevelDefs :: [DefGroup (GDef SF)]
                 -> [Export SF]
                 -> RI ([DefGroup (GDef Mem)], [Export Mem])
reprTopLevelDefs defgroups exports = go id defgroups
  where
    go hd (g:gs) = withGDefs g $ \g' -> go (hd . (g':)) gs
    go hd [] = do es <- mapM reprExport exports
                  return (hd [], es)

reprModule :: Module SF -> RI (Module Mem)
reprModule (Module mod_name [] defs exports) = do
  (defs', exports') <- reprTopLevelDefs defs exports
  return (Module mod_name [] defs' exports')

-- | Perform representation inference.
--
--   The specification type environment is used for representation inference.
representationInference :: Module SF -> IO (Module Mem)
representationInference mod = do
  -- Representation inference
  repr_mod <- withTheNewVarIdentSupply $ \supply -> do
    sf_type_env <- readInitGlobalVarIO the_systemFTypes
    type_env <- readInitGlobalVarIO the_specTypes
    dict_env <- runFreshVarM supply createDictEnv
    let context = RIEnv supply (specToTypeEnv type_env) dict_env [] sf_type_env
    runReaderT (unRI (reprModule mod)) context
  
  -- Convert from specification types to mem types
  let mem_mod = convertSpecToMemTypes repr_mod

  -- Eta-expand functions
  etaExpandModule mem_mod

-- | Convert a specification type environment to one where types can be
--   compared.  The 'mem' variant of type functions is selected.  All types
--   remain unchanged.
specToTypeEnv :: TypeEnvBase SpecMode -> TypeEnv
specToTypeEnv m = specializeTypeEnv Just Just Just m
