{-| Insert code to coerce values from one representation to another. 
    Coercions consist of code for boxing and unboxing values.
-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SystemF.ReprInference(insertCoercions)
where

import Prelude hiding(mapM, sequence)

import Control.Applicative
import Control.Monad hiding(mapM, sequence)
import Control.Monad.Reader hiding(mapM, sequence)
import Data.Traversable
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.SourcePos
import Common.Supply
import Builtins.Builtins
import SystemF.Syntax
import SystemF.MemoryIR
import Type.Compare
import Type.Environment
import Type.Eval
import Type.Substitute
import Type.Type
import Type.Var
import Globals
import GlobalVar

data Env =
  Env { boxedTypeEnv :: !(MTypeEnvBase FullyBoxedMode)
      , specTypeEnv :: !(MTypeEnvBase SpecMode)
      , memTypeEnv :: !(MTypeEnvBase UnboxedMode)
      , varIDs :: !(IdentSupply Var)
      }

newtype RI a = RI (ReaderT Env IO a)
             deriving(Functor, Applicative, Monad, MonadIO)

instance Supplies RI (Ident Var) where
  fresh = RI $ ReaderT $ \env -> supplyValue $ varIDs env

runRI :: Env -> RI a -> IO a
runRI env (RI m) = runReaderT m env

getSpecTypeEnv :: RI (MTypeEnvBase SpecMode)
getSpecTypeEnv = RI $ asks specTypeEnv

getBoxedTypeEnv :: RI (MTypeEnvBase FullyBoxedMode)
getBoxedTypeEnv = RI $ asks boxedTypeEnv

withBoxedTyping :: BoxedTypeEvalM a -> RI a
withBoxedTyping m = RI $ ReaderT $ \env ->
  runTypeEvalM m (varIDs env) (boxedTypeEnv env)

withSpecTyping :: TypeEvalM SpecMode a -> RI a
withSpecTyping m = RI $ ReaderT $ \env ->
  runTypeEvalM m (varIDs env) (specTypeEnv env)

withUnboxedTyping :: UnboxedTypeEvalM a -> RI a
withUnboxedTyping m = RI $ ReaderT $ \env ->
  runTypeEvalM m (varIDs env) (memTypeEnv env)

liftFreshVarM :: FreshVarM a -> RI a
liftFreshVarM m = RI $ ReaderT $ \env ->
  runFreshVarM (varIDs env) m

liftFreshVarMToBoxed :: FreshVarM a -> BoxedTypeEvalM a
liftFreshVarMToBoxed m = TypeEvalM $ \id_supply _ -> runFreshVarM id_supply m

-- | Add a binding to the boxed and spec type environments.
assumeType :: Var -> Type -> Type -> RI a -> RI a
assumeType v boxed_t spec_t m = do 
  boxed_type_env <- getBoxedTypeEnv
  spec_type_env <- getSpecTypeEnv
  locallyInsertType boxed_type_env v boxed_t $
    locallyInsertType spec_type_env v spec_t $
    m

-- | Add bindings to the spec type environment
assumeBindersSpec :: [Binder] -> RI a -> RI a
assumeBindersSpec bs m = foldr assumeBinderSpec m bs

-- | Add a binding to the spec type environment
assumeBinderSpec :: Binder -> RI a -> RI a
assumeBinderSpec (v ::: t) m = do
  spec_type_env <- getSpecTypeEnv
  locallyInsertType spec_type_env v t m

assumeMaybeBinderSpec :: Maybe Binder -> RI a -> RI a
assumeMaybeBinderSpec Nothing m = m
assumeMaybeBinderSpec (Just b) m = assumeBinderSpec b m
{-
unpackFunT :: Type -> RI (Type, Type)
unpackFunT ty = do
  ty' <- reduceToWhnf ty
  case ty' of
    d `FunT` r -> return (d, r)
    _ -> internalError "unpackFunT: Not a function type"
-}

-- | Get the type of a function.
sfFunctionType :: FunSF -> Type 
sfFunctionType (FunSF (Fun { funTyParams = ty_params
                           , funParams = params
                           , funReturn = ret
                           })) =
  forallType [b | TyPat b <- ty_params] $
  funType [t | VarP _ t <- params] ret

-- | Deconstruct a spec kind
deconSpecArrowKind :: Kind -> (Kind, Kind)
deconSpecArrowKind (k1 `FunT` k2) = (k1, k2)

-- | An 2-tuple with infix constructor syntax, for syntactic convenience
infix 5 :*
data a :* b = a :* b

-- | Given a spec type that exactly has the form @c t@, return @t@
unapply :: Var -> Type -> RI Type
unapply con ty = do
  Just (op_var, [arg]) <- withSpecTyping $ deconVarAppType ty
  if op_var == con
    then return arg
    else internalError "unapply"

-- | Apply a constructor or type function to @t@
apply :: Var -> Type -> RI Type 
apply con ty = return $ con `varApp` [ty]

-- | Check whether the expression is annotated as being an uncoercible value.
--   This occurs on coercion terms.
isUncoercibleValue :: ExpSF -> Bool
isUncoercibleValue e =
  case fromExpSF e
  of -- Look through 'let', 'letfun', and 'case' expressions 
     LetE {expBody = b} -> isUncoercibleValue b
     LetfunE {expBody = b} -> isUncoercibleValue b
     CaseE {expAlternatives = (AltSF (Alt {altBody = b}) : _)} ->
       isUncoercibleValue b
     _ -> case getExpRepresentation e
          of ValueRepresentation -> True
             _ -> False

-- | Check whether the fully boxed type is an uncoercible type.
--
--   The following equivalence should always hold:
--
-- > isUncoercibleType (typeOf e) <-> isUncoercibleValue e
isUncoercibleType :: Type -> Bool
isUncoercibleType ty =
  case fromTypeApp (strip_foralls ty)
  of (CoT {}, [_, _]) -> True
     _ -> False
  where
    strip_foralls (AllT _ t) = strip_foralls t
    strip_foralls t = t

-------------------------------------------------------------------------------
-- Kind conversion

-- | Convert a fully boxed kind to a core boxed kind
toBoxedKind :: Kind -> Kind
toBoxedKind k = k               -- This is just the identity transformation

-- | Convert a core kind to the corresponding boxed kind
coreToBoxedKind :: Kind -> Kind
coreToBoxedKind (VarT k)
  | k == boxV      = boxT
  | k == bareV     = boxT
  | k == valV      = boxT
  | k == intindexV = intindexT

coreToBoxedKind (k1 `FunT` k2) = coreToBoxedKind k1 `FunT` coreToBoxedKind k2

coreToBoxedKind _ = internalError "coreToBoxedKind: Unexpected kind"

-- | Convert a spec type from one kind to another.
(|>) :: Kind -> Kind -> Type -> RI Type
(k1 |> k2) t = kindCoerce k1 k2 t

-- | Convert a spec type from one spec kind to another.
kindCoerce :: Kind -> Kind -> Type -> RI Type
kindCoerce k1 k2 t =
  case (k1, k2) of
    -- Conversion between kinds of proper types
    (VarT v1, VarT v2)
      | v1 == v2                   -> return t
      | v1 == valV && v2 == bareV  -> apply storedV t
      | v1 == bareV && v2 == valV  -> unapply storedV t
      | v1 == bareV && v2 == initV -> apply initConV t
      | v1 == initV && v2 == bareV -> unapply initConV t
      | v1 == bareV && v2 == boxV  -> apply (coreBuiltin The_AsBox) t
      | v1 == boxV && v2 == bareV  -> apply (coreBuiltin The_AsBare) t
      | otherwise                  -> kindCoerce k1 bareT t >>=
                                      kindCoerce bareT k2

    -- Conversion between function kinds.
    (d1 `FunT` r1, d2 `FunT` r2) ->
      -- If kinds are equal, do nothing
      ifM (withSpecTyping $ compareTypes d1 d2 >&&> compareTypes r1 r2)
      (return t)
      (do
        -- Otherwise,
        -- create a coercion function (\a:d2. (r1 |> r2) (t ((d2 |> d1) a)))
        a <- newVar Nothing TypeLevel
        a' <- kindCoerce d2 d1 (VarT a) -- Coerce domain
        t_a <- kindCoerce r1 r2 (AppT t a') -- Coerce range
        return $ LamT (a ::: d2) t_a)

    _ -> internalError $
         "No kind coercion for " ++
         show (pprType k1) ++ ", " ++ show (pprType k2)

-- | Elaborate a type to its natural representation
elaborateType :: Type -> RI (Type, Kind)
elaborateType ty = do
  ty' <- withBoxedTyping $ reduceToWhnf ty
  elaborated <-
    case ty'
    of VarT v -> return $ VarT v
       t1 `AppT` t2 -> do
         -- Elaborate the operator and deconstruct its kind
         (t1', k1') <- elaborateType t1
         let (k_d, k_r) = deconSpecArrowKind k1'

         -- Elaborate the operand and coerce to the given kind
         t2' <- elaborateTypeTo k_d t2
         return $ t1' `AppT` t2'

       AllT (a ::: k) t ->
         -- Add the boxed kind 'k' to both the boxed and spec type environments
         assumeType a k k $ do
           -- Elaborate to boxed or uncoercible value types
           t' <- elaborateBaseTypeToForm BoxedT t
           return $ AllT (a ::: k) t'

       d `FunT` r -> do
         -- Elaborate to boxed or uncoercible value types
         d' <- elaborateBaseTypeToForm BoxedT d
         r' <- elaborateBaseTypeToForm BoxedT r
         return $ d' `FunT` r'

       CoT k ->
         return (CoT (toBoxedKind k))

       IntT n ->
         return (IntT n)

       _ -> internalError $ "elaborateType: " ++ show (pprType ty)

  kind <- withSpecTyping $ typeKind elaborated
  return (elaborated, kind)

-- | Elaborate a type to a specific kind
elaborateTypeTo :: Kind -> Type -> RI Type
elaborateTypeTo wanted_k t = do
  (t', natural_k) <- elaborateType t
  (natural_k |> wanted_k) t'

-- | What form to elaborate a type to
data TypeForm =
    BoxedT                    -- ^ Elaborate to a boxed type, /unless/
                              --   it's an uncoercible value type, in
                              --   which case elaborate to a value type.
  | NaturalT                  -- ^ Elaborate to a natural type.  The head
                              --   of the type should be an arrow or
                              --   data type constructor.
  | ValOrBoxedT               -- ^ Elaborate to a value or boxed type.
                              --   The head
                              --   of the type should be an arrow or
                              --   data type constructor.

-- | Elaborate an inhabited type, using the given strategy to select 
--   the elaborated type.
elaborateBaseTypeToForm :: TypeForm -> Type -> RI Type
elaborateBaseTypeToForm form ty = do
  (ty', k) <- elaborateType ty
  case form of
    NaturalT -> return ty'
    ValOrBoxedT ->                      
      case k
      of VarT kv
           | kv == valV || kv == boxV -> return ty'
           | kv == bareV              -> apply (coreBuiltin The_AsBox) ty'
    BoxedT ->
      if isUncoercibleType ty
      then return ty'           -- Return the natural type
      else  (k |> boxT) ty'

-- | Convert a core type to its natural form.
--   The type must be of the form @C ts@, @t1 ~ t2@, or @forall as. t1 -> t2@.
naturalType :: Type -> RI Type
naturalType ty = do
  k <- withSpecTyping $ typeKind ty

  natural_kind <-
    condM (strip_foralls_and_coercions ty)
    [ -- Function type
      do FunT {} <- it
         return boxT

    , -- Data type
      do ty' <- it
         Just (con, _) <- return $ fromVarApp ty'
         Just dtype <- lift $ withSpecTyping $ lookupDataType con

         -- Convert to the natural kind for this data type
         return $ fromBaseKind (dataTypeKind dtype)

    , -- Coercion types are values
      do ty' <- it
         (CoT {}, [_, _]) <- return $ fromTypeApp ty'
         return valT

    , lift $ internalError $
      "naturalType: Not a function or data type: " ++ show (pprType ty)
    ]

  -- Coerce type
  (k |> natural_kind) ty
  where
    -- Remove all forall and adapter terms from the head of this type
    strip_foralls_and_coercions ty =
      condM (withSpecTyping $ reduceToWhnf ty)
      [ do AllT _ t' <- it
           lift $ strip_foralls_and_coercions t'

      , do AppT (VarT con) t' <- it
           aguard $ isAdapterCon con
           lift $ strip_foralls_and_coercions t'

      , it
      ]

-------------------------------------------------------------------------------
-- Type conversion

-- | An elaborated expression.  The expression is annotated with
--   information that may be needed for type conversion.
data EExp =
  EExp
  { eeType :: !Type             -- ^ The expression's spec type
  , eeExp :: !ExpM              -- ^ The elaborated expression
  }

type Rep = Representation

infix 4 |>>
-- | Convert an expression from one spec type to another.
(|>>) :: Rep :* Type            -- Convert from type
      -> Type                   -- Convert to type
      -> ExpM                   -- Convert this expression
      -> RI ExpM                -- Compute the coerced expression
(rep :* t1 |>> t2) expression = do
  kindCoerceExp rep t1 t2 expression

kindCoerceExp :: Rep -> Type -> Type -> ExpM -> RI ExpM
kindCoerceExp rep t1 t2 expression = do
  -- Determine which storage strategies are being used
  k1 <- withSpecTyping $ typeBaseKind t1
  k2 <- withSpecTyping $ typeBaseKind t2

  case (k1, k2) of
    -- No coercion required    
    _ | k1 == k2 -> return expression

    -- Store into memory
    (ValK, WriteK) -> stored_con t1 expression

    -- Store into a new heap object, return a reference to its contents
    (ValK, BareK) -> allocate_boxed_storage t2 =<< stored_con t1 expression

    -- Store into a new heap object
    (ValK, BoxK) -> let bare_type = storedV `varApp` [t1]
                    in boxed_con bare_type =<< stored_con t1 expression

    -- Load from memory
    (BareK, ValK) -> stored_decon t2 expression

    -- Copy
    (BareK, WriteK) -> copy t1 expression

    -- Copy into a new heap object
    (BareK, BoxK) -> convert_to_boxed t1 =<< copy t1 expression

    -- Store into a new heap object, then read its contents
    (WriteK, ValK) -> let bare_type = storedV `varApp` [t2]
                      in stored_decon t2 =<<
                           allocate_boxed_storage bare_type expression

    -- Write into a new heap object, return a reference to its contents
    (WriteK, BareK) -> allocate_boxed_storage t2 expression

    -- Write into a new heap object
    (WriteK, BoxK) -> do bare_type <- unapply initConV t1
                         convert_to_boxed bare_type expression

    -- Read contents of boxed object
    (BoxK, ValK) -> let bare_type = storedV `varApp` [t2]
                    in stored_decon t2 =<< boxed_decon bare_type expression

    -- Copy contents of boxed object
    (BoxK, WriteK) -> do bare_type <- unapply initConV t2
                         convert_to_bare bare_type expression

    -- Read contents of boxed object
    (BoxK, BareK) -> allocate_boxed_storage t2 =<<
                       convert_to_bare t2 expression
  where
    exp_info = case expression of ExpM e -> mkExpInfo (getSourcePos e)

    stored_con val_type e = do
      let con_inst = VarCon stored_conV [val_type] []
      return $ conE exp_info con_inst [] Nothing [e]

    boxed_con bare_type e = do
      let con_inst = VarCon (coreBuiltin The_boxed) [bare_type] []

      -- Create a type object and a 
      -- size parameter holding the size of the boxed object
      rep <- rep_e bare_type
      type_info <- withSpecTyping $
                   boxedDataInfo exp_info (coreBuiltin The_boxed)
                   [bare_type] [rep]
      let size_param =
            varAppE exp_info (coreBuiltin The_reprSizeAlign) [bare_type] [rep]
      return $ conE exp_info con_inst [size_param] (Just type_info) [e]

    stored_decon val_type e = do
      x <- newAnonymousVar ObjectLevel
      let decon = VarDeCon stored_conV [val_type] []
      return $ ExpM $ CaseE exp_info e []
        [AltM $ Alt decon Nothing [patM (x ::: val_type)] (varE' x)]

    boxed_decon bare_type e = do
      x <- newAnonymousVar ObjectLevel
      rep <- rep_e bare_type

      -- Create pattern for the type object
      ty_ob <- newAnonymousVar ObjectLevel
      Just boxed_type <- withUnboxedTyping $ lookupDataType $ coreBuiltin The_Boxed
      info_type <- withUnboxedTyping $ instantiateInfoType boxed_type [bare_type]
      let ty_ob_pat = patM (ty_ob ::: info_type)
      
      let decon = VarDeCon (coreBuiltin The_boxed) [bare_type] []

      -- Create a size parameter holding the size of the boxed object
      let size_param =
            varAppE exp_info (coreBuiltin The_reprSizeAlign) [bare_type] [rep]
      
      return $ ExpM $ CaseE exp_info e [size_param]
        [AltM $ Alt decon (Just ty_ob_pat) [patM (x ::: bare_type)] (varE' x)]

    -- Write into a new boxed object, then return a bare reference
    allocate_boxed_storage bare_type e = do
      let con = VarCon (coreBuiltin The_stuckBox) [bare_type] []
          decon = VarDeCon (coreBuiltin The_stuckBox) [bare_type] []
      rep <- rep_e bare_type
      type_info <- withSpecTyping $
                   boxedDataInfo exp_info (coreBuiltin The_stuckBox)
                   [bare_type] [rep]

      -- Create pattern for the type object
      ty_ob <- newAnonymousVar ObjectLevel
      Just stuckbox_type <- withUnboxedTyping $ lookupDataType $ coreBuiltin The_StuckBox
      info_type <- withUnboxedTyping $ instantiateInfoType stuckbox_type [bare_type]
      let ty_ob_pat = patM (ty_ob ::: info_type)

      -- Create a size parameter holding the size of the boxed object
      let size_param =
            varAppE exp_info (coreBuiltin The_reprSizeAlign) [bare_type] [rep]

      let boxed_expr = conE exp_info con [size_param] (Just type_info) [e]
      x <- newAnonymousVar ObjectLevel
      return $ ExpM $ CaseE exp_info boxed_expr [size_param]
        [AltM $ Alt decon (Just ty_ob_pat) [patM (x ::: bare_type)] (varE' x)]

    -- Get the representation dictionary as an expression 
    rep_e bare_type =
      case rep
      of Representation e -> do
           (_, e') <- elaborateExpressionBoxed e 
           return e'
         BoxedRepresentation ->
           return $ appE exp_info (varE' (coreBuiltin The_repr_Box))
                    [coreBuiltin The_AsBox `varApp` [bare_type]] []
         ValueRepresentation ->
           -- Should never need coercions for this type
           internalError "kindCoerceExp"

    copy bare_type e = do
      dict <- rep_e bare_type
      return $ appE exp_info (varE' (coreBuiltin The_copy)) [bare_type] [dict, e]

    convert_to_bare bare_type e = do
      dict <- rep_e bare_type
      return $ appE exp_info (varE' (coreBuiltin The_asbare)) [bare_type] [dict, e]

    convert_to_boxed bare_type e = do
      dict <- rep_e bare_type
      return $ appE exp_info (varE' (coreBuiltin The_asbox)) [bare_type] [dict, e]

-- | Elaborate a binder to the given type.  Add the fully boxed type to the
-- environment.
elaborateBinderTo :: PatSF -> Type -> (PatM -> RI a) -> RI a
elaborateBinderTo (VarP v boxed_ty) ty k =
  assumeType v boxed_ty ty $ k (patM (v ::: ty))

-- | Elaborate a binder to a boxed type
elaborateBinder :: TypeForm -> PatSF -> (PatM -> RI a) -> RI a
elaborateBinder form (VarP v ty) k = do
  ty' <- elaborateBaseTypeToForm form ty
  assumeType v ty ty' $ k (patM (v ::: ty'))

elaborateBinders :: TypeForm -> [PatSF] -> ([PatM] -> RI a) -> RI a
elaborateBinders form pats k = withMany (elaborateBinder form) pats k

elaborateTyBinder :: TyPat -> (TyPat -> RI a) -> RI a
elaborateTyBinder (TyPat (v ::: kind)) k = do
  -- Add a fully boxed type to the type environment
  assumeType v kind kind $ k (TyPat (v ::: toBoxedKind kind))

elaborateTyBinders :: [TyPat] -> ([TyPat] -> RI a) -> RI a
elaborateTyBinders pats k = withMany elaborateTyBinder pats k

-- | What form to elaborate an expression to
data ElaboratedForm =
    AnyForm
  | NaturalForm                 -- ^ Elaborate to kind with no wrapper types
  | BoxedForm                   -- ^ Elaborate to boxed kind
  | GivenType Type              -- ^ Elaborate to the given spec type

elaborateExpression :: ExpSF -> RI EExp
elaborateExpression expression = elaborateExpression' AnyForm expression

-- | Elaborate an expression.  If a target spec type is given, the
--   elaborated expression will be converted to that type.
elaborateExpressionTo :: Type -> ExpSF -> RI ExpM
elaborateExpressionTo target_ty expression = do
  e <- elaborateExpression' (GivenType target_ty) expression
  return $ eeExp e

-- | Elaborate an expression to a boxed type.
elaborateExpressionBoxed :: ExpSF -> RI (Type, ExpM)
elaborateExpressionBoxed expression = do
  eexp <- elaborateExpression' BoxedForm expression
  return (eeType eexp, eeExp eexp)

-- | Elaborate an expression to its natural type.  This is only called in
--   contexts where the head is an arrow or data type constructor.
elaborateExpressionNatural :: ExpSF -> RI (Type, ExpM)
elaborateExpressionNatural expression = do
  eexp <- elaborateExpression' NaturalForm expression
  return (eeType eexp, eeExp eexp)

-- | Elaborate an expresison.  If a target type is given, the elaborated
--   expression will be converted to that type.
elaborateExpression' :: ElaboratedForm -> ExpSF -> RI EExp
elaborateExpression' form expression =
  case fromExpSF expression
  of VarE _ v -> coerce =<< elaborateVar info rep v
     LitE _ l -> coerce =<< elaborateLit info rep l
     ConE _ con to sps args -> coerce =<< elaborateCon info rep con to sps args
     AppE _ op ty_args args -> coerce =<< elaborateApp info rep op ty_args args
     LamE _ f -> coerce =<< elaborateLam info rep f

     -- Let, letfun, and case are not annotated with 'rep' terms
     LetE _ b rhs body -> elaborateLet info form b rhs body
     LetfunE _ defs b -> elaborateLetfun info form defs b
     CaseE _ scr sps alts -> elaborateCase info form scr sps alts

     CoerceE _ t t' body -> coerce =<< elaborateCoerce info rep t t' body
     ArrayE _ ty elts -> coerce =<< elaborateArray info rep ty elts
  where
    coerce e = coerceExpressionResult form rep e
    info = mkExpInfo (getSourcePos expression)
    rep = getExpRepresentation expression

-- | Coerce the expression to the given type if one was given.  Otherwise,
--   return it.
coerceExpressionResult :: ElaboratedForm -> Rep -> EExp -> RI EExp
coerceExpressionResult form rep e =
  case form
  of AnyForm -> return e
     BoxedForm -> coerce_to_kind boxT
     NaturalForm -> coerce_to_type =<< naturalType (eeType e)
     GivenType t -> coerce_to_type t
  where
    coerce_to_kind want_k = do
      given_k <- withSpecTyping $ typeKind $ eeType e
      want_t <- (given_k |> want_k) (eeType e)
      coerce_to_type want_t

    coerce_to_type want_t = do
      e' <- (rep :* eeType e |>> want_t) (eeExp e)
      return $ EExp want_t e'

elaborateVar info rep v = do
  Just ty <- withSpecTyping $ lookupType v
  return $ EExp ty (ExpM $ VarE info v)

elaborateLit info rep l = do
  let ty = literalType l
  return $ EExp ty (ExpM $ LitE info l)

elaborateCon info rep con ty_obj sps args = do
  (con', field_types, result_type) <- elaborateConInst con
  ty_obj' <- mapM (fmap snd . elaborateExpressionNatural) ty_obj
  sps' <- mapM (fmap snd . elaborateExpressionNatural) sps
  args' <- zipWithM elaborateExpressionTo field_types args
  return $ EExp result_type (ExpM $ ConE info con' ty_obj' sps' args')

-- | Elaborate a data constructor instance.  Compute the elaborated
-- parameter and return types.
elaborateConInst :: ConInst -> RI (ConInst, [Type], Type)
elaborateConInst (VarCon con ty_args ex_types) = do
  Just dcon_type <- withSpecTyping $ lookupDataCon con
  let typaram_kinds = map binderType $ dataConTyParams dcon_type
      ex_type_kinds = map binderType $ dataConExTypes dcon_type

  -- Coerce type arguments
  ty_args' <- zipWithM elaborateTypeTo typaram_kinds ty_args
  ex_types' <- zipWithM elaborateTypeTo ex_type_kinds ex_types

  -- Compute field types, using the spec type environment.
  -- This is a hack because we're using the mem type 
  -- These types agree with the mem type environment since we don't allow
  -- boxed types.
  (data_field_types, data_return_type) <-
    withSpecTyping $
    instantiateDataConTypeWithExistentials dcon_type (ty_args' ++ ex_types')
  field_types <- withSpecTyping $ mapM toInitializerType data_field_types
  return_type <- withSpecTyping $ toInitializerType data_return_type

  return (VarCon con ty_args' ex_types', field_types, return_type)

-- | Elaborate a data deconstructor instance.  Compute the elaborated
-- parameter and return types.
elaborateDeConInst :: DeConInst -> RI (DeConInst, [Type])
elaborateDeConInst (VarDeCon con ty_args []) = do
  Just dcon_type <- withSpecTyping $ lookupDataCon con
  let typaram_kinds = map binderType $ dataConTyParams dcon_type

  -- Coerce type arguments
  ty_args' <- zipWithM elaborateTypeTo typaram_kinds ty_args

  -- Compute field types
  ([], field_types, _) <-
    withSpecTyping $ instantiateDataConType dcon_type ty_args' []

  return (VarDeCon con ty_args' [], field_types)

-- | If the type is a bare type, convert to a spec initializer type.
toInitializerType :: Type -> TypeEvalM SpecMode Type
toInitializerType ty = do
  k <- typeBaseKind ty
  return $! case k
            of BareK -> initConV `varApp` [ty]
               BoxK  -> ty
               ValK  -> ty

elaborateApp info rep op ty_args args = do
  (op_type, op') <- elaborateExpressionNatural op
  (inst_op_type, ty_args') <- elaborateTypeApplications op_type ty_args
  (return_type, args') <- elaborateValueApplications inst_op_type args
  return $ EExp return_type (ExpM $ AppE info op' ty_args' args')

-- | Given a Spec operator type and boxed argument types, elaborate the
--   argument types
elaborateTypeApplications :: Type -> [Type] -> RI (Type, [Type])
elaborateTypeApplications op_type arg_types = go id op_type arg_types 
  where
    go hd op_type (ty:tys) = do
      Right (x ::: dom, rng) <- withBoxedTyping $ deconAllType op_type

      -- Convert 'ty' to kind 'dom'
      ty' <- elaborateTypeTo dom ty

      -- Instantiate type 
      rng' <- withSpecTyping $ substituteVar x ty' rng
      go (hd . (ty':)) rng' tys

    go hd op_type [] = return (op_type, hd [])

elaborateValueApplications :: Type -> [ExpSF] -> RI (Type, [ExpM])
elaborateValueApplications op_type args = go id op_type args
  where
    go hd op_type (arg:args) = do
      Right (dom, rng) <- withBoxedTyping $ deconFunType op_type

      -- Elaborate the argument to match the expected type
      arg' <- elaborateExpressionTo dom arg
      go (hd . (arg':)) rng args

    go hd op_type [] = return (op_type, hd [])

elaborateLam info rep f = do
  f' <- elaborateFun f
  let ty = functionType f'
  return $ EExp ty (ExpM $ LamE info f')

elaborateLet info target_type binder@(VarP v binder_type) rhs body = do
  -- Convert the RHS to its natural representation, if it's an uncoercible
  -- value.  Otherwise, convert to a boxed representation.
  (ty, rhs') <- if isUncoercibleType binder_type
                then elaborateExpressionNatural rhs
                else elaborateExpressionBoxed rhs
  elaborateBinderTo binder ty $ \binder' -> do
    EExp ty body' <- elaborateExpression' target_type body
    return $ EExp ty (ExpM $ LetE info binder' rhs' body')

elaborateLetfun :: ExpInfo -> ElaboratedForm -> DefGroup (FDef SF) -> ExpSF
                -> RI EExp
elaborateLetfun info target_type (Rec defs) body = do
  def_types <- mk_def_types
  assumeBindersSpec def_types $ do
    defs' <- mapM elaborateFunDef defs
    EExp ty body' <- elaborateExpression' target_type body
    return $ EExp ty (ExpM $ LetfunE info (Rec defs') body')
  where
    -- Elaborate the types of all functions
    mk_def_types =
      sequence [do ty <- elaborateFunctionType $ definiens d
                   return (definiendum d ::: ty)
               | d <- defs]

elaborateLetfun info target_type (NonRec def) body = do
  def' <- elaborateFunDef def
  assumeBinderSpec (definiendum def ::: functionType (definiens def')) $ do
    EExp ty body' <- elaborateExpression' target_type body
    return $ EExp ty (ExpM $ LetfunE info (NonRec def') body')

elaborateCase info target_type scr sps alts = do
  (_, scr') <- elaborateExpressionNatural scr
  sps' <- mapM (fmap snd . elaborateExpressionNatural) sps
  (result_type, alts') <- elaborateAlts target_type alts
  return $ EExp result_type (ExpM $ CaseE info scr' sps' alts')

elaborateAlts target_type alts = do
  (result_types, alts') <- mapAndUnzipM (elaborateAlt target_type) alts
  return (head result_types, alts')

elaborateAlt :: ElaboratedForm -> AltSF -> RI (Type, AltM)
elaborateAlt target_type (AltSF (Alt decon m_tyob params body)) = do
  (decon', field_types) <- elaborateDeConInst decon
  let params' = [patM (v ::: ty) | (VarP v _, ty) <- zip params field_types]

  -- Type object binder
  m_ty_ob' <-
    case m_tyob
    of Nothing -> return Nothing
       Just (VarP v _) ->
         withUnboxedTyping $ do
           -- This is a boxed algebraic data type pattern
           let VarDeCon con _ _ = decon'
           Just dcon_type <- lookupDataCon con
           unless (dataTypeKind (dataConType dcon_type) == BoxK) $ 
             internalError "elaborateAlt"
           info_ty <-
             instantiateInfoType (dataConType dcon_type) (deConTyArgs decon')
           return $ Just $ patM (v ::: info_ty)

  assumeMaybeBinderSpec (fmap patMBinder m_ty_ob') $
    assumeBindersSpec (map patMBinder params') $ do
      EExp result_type body' <- elaborateExpression' target_type body
      return (result_type, AltM (Alt decon' m_ty_ob' params' body'))

elaborateCoerce info rep t t' body = do
  -- Convert types.  Make sure they have the same kind.  Use the natural
  -- representation of the types.
  (elaborated_t, k) <- elaborateType t
  elaborated_t' <- elaborateTypeTo k t'
  body' <- elaborateExpressionTo elaborated_t body
  return $ EExp elaborated_t' (ExpM $ CoerceE info elaborated_t elaborated_t' body') 

elaborateArray info rep elt_type elts = do
  -- Array elements must be bare
  bare_elt_type <- elaborateTypeTo bareT elt_type
  let init_elt_type = initConT `typeApp` [bare_elt_type]

  -- Elaborate all array elements
  elts' <- mapM (elaborateExpressionTo init_elt_type) elts

  -- Result is an array of this type
  let n = fromIntegral $ length elts
  let result_type = initConT `typeApp` [arrT `typeApp` [IntT n, bare_elt_type]]
  return $ EExp result_type (ExpM $ ArrayE info bare_elt_type elts')

elaborateExportedFun f = elaborateFun_ True f
elaborateFun f = elaborateFun_ False f

-- | Elaborate a function.
--
--   The 'ElaboratedForm' argument determines how function parameter
--   types are elaborated.  In most cases, functions are elaborated to a
--   fully boxed type.  However, functions exported to C++ are elaborated
--   to a natural type, which makes them easier to call.
elaborateFun_ is_export (FunSF (Fun inf ty_params params ret_type body)) =
  check_form $
  withMany elaborateTyBinder ty_params $ \ty_params' -> do
    ret_type' <- elaborateBaseTypeToForm return_form ret_type
    elaborateBinders parameter_form params $ \params' -> do
      body' <- elaborateExpressionTo ret_type' body
      return $ FunM $ Fun inf ty_params' params' ret_type' body'
  where
    !(parameter_form, return_form) =
      if is_export
      then (NaturalT, ValOrBoxedT)
      else (BoxedT, BoxedT)

    -- Check parameter values.  Return 'x' or throw an error.
    check_form x
      | is_export =
          -- Only monomorphic functions are allowed to be exported
          if Prelude.null ty_params then x else internalError "elaborateFun"
      | otherwise = x

-- | Elaborate a function defintion.  The function name has already been
--   added to the environment (if appropriate).
elaborateFunDef d = mapMDefiniens elaborateFun d

elaborateGlobalDef d = mapMDefiniens elaborate_global d
  where
    elaborate_global (FunEnt f) = FunEnt `liftM` elaborateFun f
    elaborate_global (DataEnt c) = DataEnt `liftM` elaborateConstant c

-- | Elaborate a constant to its natural type
elaborateConstant (Constant inf ty e) = do
  (ty', k) <- elaborateType ty
  e' <- elaborateExpressionTo ty' e
  return $ Constant inf ty' e'

-- | Compute the elaborated type of a function.  This is used when
--   the type is needed before the function itself is elaborated.
elaborateFunctionType :: Fun SF -> RI Type
elaborateFunctionType f = do
  (ty, _) <- elaborateType $ sfFunctionType f
  return ty

-- | Compute the elaborated type of a constant.  This is used when the
--   type is needed before the constant itself is elaborated.
elaborateConstantType :: Constant SF -> RI Type
elaborateConstantType c = do
  (ty, _) <- elaborateType $ constType c
  return ty

elaborateGlobalGroup :: DefGroup (GDef SF)
                     -> (DefGroup (GDef Mem) -> RI a)
                     -> RI a
elaborateGlobalGroup (Rec defs) k = do
  def_types <- mk_def_types
  assumeBindersSpec def_types $ do
    k . Rec =<< mapM elaborateGlobalDef defs
  where
    mk_def_types =
      sequence [do ty <- case definiens d
                         of FunEnt f -> elaborateFunctionType f
                            DataEnt c -> elaborateConstantType c
                   return (definiendum d ::: ty)
               | d <- defs]

elaborateGlobalGroup (NonRec def) k = do
  def' <- elaborateGlobalDef def
  assumeBinderSpec (definiendum def' ::: entityType (definiens def')) $
    k (NonRec def')

elaborateExport (Export pos spec f) = do
  f' <- elaborateExportedFun f
  return $ Export pos spec f'

elaborateModule :: Module SF -> RI (Module Mem)
elaborateModule (Module mod_name [] groups exports) = do
  (groups', exports') <- do_groups id groups
  return $ Module mod_name [] groups' exports'
  where
    do_groups hd (g:gs) =
      elaborateGlobalGroup g $ \g' -> do_groups (hd . (g':)) gs

    do_groups hd [] = do
      exports' <- mapM elaborateExport exports
      return (hd [], exports')

insertCoercions :: Module SF -> IO (Module Mem)
insertCoercions mod = do
  withTheNewVarIdentSupply $ \supply -> do
    boxed_type_env <- thawTypeEnv =<< readInitGlobalVarIO the_systemFTypes
    spec_type_env <- thawTypeEnv =<< readInitGlobalVarIO the_specTypes
    unboxed_type_env <- thawTypeEnv =<< readInitGlobalVarIO the_memTypes
    let env = Env boxed_type_env spec_type_env unboxed_type_env supply
    runRI env (elaborateModule mod)
