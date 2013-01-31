
{-# LANGUAGE Rank2Types #-}
module CParser2.GenCode2 (createCoreModule) where

import Control.Monad
import Control.Monad.Reader

import Common.MonadLogic
import Common.Identifier
import Common.SourcePos
import Common.Supply
import Common.Error
import Common.Label
import Builtins.TypeFunctions
import CParser2.AST
import CParser2.AdjustTypes
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import qualified SystemF.Syntax as SystemF
import qualified SystemF.MemoryIR as SystemF
import qualified SystemF.SpecToMem as SystemF
import qualified SystemF.Typecheck
import qualified SystemF.TypecheckMem
import Type.Environment
import qualified Type.Compare
import qualified Type.Eval
import Type.Var
import Type.Type(Binder(..), Level(..))
import qualified Type.Type as Type

-- | Partition a module into expression declarations and type declarations.
partitionModule :: Module Resolved
                -> ([LDecl Resolved], [LDecl Resolved])
partitionModule mod@(Module decls) =
  partition is_value_decl decls
  where
    is_value_decl ldecl =
      case unLoc ldecl
      of Decl _ (FunEnt {})   -> True
         Decl _ (ConstEnt {}) -> True
         _                    -> False

newtype UpdateTypeEnv = UpdateTypeEnv (SpecTypeEnv -> SpecTypeEnv)

instance Monoid UpdateTypeEnv where
  mempty = UpdateTypeEnv id
  UpdateTypeEnv f `mappend` UpdateTypeEnv g = UpdateTypeEnv (f . g)

applyUpdates :: UpdateTypeEnv -> SpecTypeEnv -> SpecTypeEnv
applyUpdates (UpdateTypeEnv f) e = f e

toVar (ResolvedVar v) = v

showResolvedVar = show . toVar

-- | Extract information from an attribute list on a variable declaration
fromVarAttrs :: [Attribute] -> Bool
fromVarAttrs attrs =
  -- Start with default attributes and modify given each attribute
  foldl' interpret False attrs
  where
    interpret st ConlikeAttr = True

    -- Ignore inlining attributes
    interpret st InlineAttr = st
    interpret st InlineSequentialAttr = st
    interpret st InlineDimensionalityAttr = st
    interpret st InlineFinalAttr = st
    interpret st InlinePostfinalAttr = st

    interpret st _ =
      error "Unexpected attribute on type declaration"

-------------------------------------------------------------------------------
-- Type translation

-- | A mapping from "let type"-bound identifiers to types.
type LetTypeEnv = Map.Map Var Type.Type

data TransTEnv =
  TransTEnv 
  { envLetTypes :: LetTypeEnv 
  , envSpecTypes :: SpecTypeEnv 
  , envTypeFunctions :: Map.Map String BuiltinTypeFunction
  }

newtype TransT a = TransT (Reader TransTEnv a)

instance Monad TransT where
  return x = TransT (return x)
  TransT m >>= k = TransT (m >>= \x -> case k x of TransT m' -> m')

instance TypeEnvMonad TransT where
  type TypeFunctionInfo TransT = BuiltinTypeFunction
  getTypeEnv = TransT (asks envSpecTypes)
  askTypeEnv f = TransT (asks (f . envSpecTypes))

  assumeWithProperties v t b (TransT m) = TransT (local insert m)
    where
      insert e = e {envSpecTypes = insertTypeWithProperties v t b $
                                   envSpecTypes e}

runTypeTranslation :: SpecTypeEnv -> Map.Map String BuiltinTypeFunction
                   -> TransT a -> a
runTypeTranslation tenv type_functions (TransT m) =
  runReader m (TransTEnv Map.empty tenv type_functions)

class HasLetSynonym m where
  lookupLetTypeSynonym :: ResolvedVar -> m (Maybe Type.Type)
  withLetTypeSynonym :: ResolvedVar -> Type.Type -> m a -> m a

instance HasLetSynonym TransT where
  lookupLetTypeSynonym v = TransT $ asks (Map.lookup (toVar v) . envLetTypes)

  withLetTypeSynonym v t (TransT m) = TransT $ local insert m
    where
      insert e = e {envLetTypes = Map.insert (toVar v) t $ envLetTypes e}

lookupBuiltinTypeFunction :: String -> TransT (Maybe BuiltinTypeFunction)
lookupBuiltinTypeFunction name = TransT $ asks lookup_name
  where
    lookup_name env = Map.lookup name $ envTypeFunctions env

-------------------------------------------------------------------------------
-- First-pass type translation.
--
-- Create a type environment containing kinds only.

-- | Translate a global type-related declaration.
declKind :: LDecl Resolved -> TransT UpdateTypeEnv
declKind (L loc (Decl ident ent)) = do
  let make_update kind =
        return $ UpdateTypeEnv $ insertType (toVar ident) kind
  case ent of
    TypeEnt   kind           -> typeExpr kind >>= make_update
    DataEnt binders kind _ _ -> typeExpr (fun_kind binders kind) >>= make_update
    _                        -> return mempty
  where
    fun_kind bs k = foldr fun_t k bs
      where
        fun_t (Domain _ (Just dom)) rng = L loc (dom `FunT` rng)

-- | Create a kind environment from the given declarations
declKindEnvironment :: [LDecl Resolved] -> TransT UpdateTypeEnv
declKindEnvironment decls = liftM mconcat $ mapM declKind decls

-------------------------------------------------------------------------------
-- Second-pass type translation.
--
-- Create a type environment containing type information.

-- | Compute the kind of a translated AST type
typeKind :: TypeEnvMonad m => Type.Type -> m Type.Kind
typeKind ty = do
  tenv <- getTypeEnv 
  return $ Type.Eval.typeKind tenv ty

-- | Translate a domain that must have an explicit type
domain :: (HasLetSynonym m, TypeEnvMonad m) =>
          Domain Resolved -> (Type.Binder -> m a) -> m a
domain (Domain param (Just ty)) k = do
  let v = toVar param
  t <- typeExpr ty
  assume v t $ k (v ::: t)

domain (Domain _ Nothing) _ =
  -- This error should have been caught during parsing
  internalError "domain: Missing type annotation"

-- | Translate a list of domains that must have explicit types
domains :: (HasLetSynonym m, TypeEnvMonad m) =>
           [Domain Resolved] -> ([Type.Binder] -> m a) -> m a
domains = withMany domain

typeExprs = mapM typeExpr

-- | Translate an AST type to a specification type and compute its kind.
typeAndKind :: (HasLetSynonym m, TypeEnvMonad m) =>
               RLType -> m (Type.Type, Type.Kind)
typeAndKind lty = do
  ty <- typeExpr lty
  k <- typeKind ty
  return (ty, k)

-- | Translate an AST type or kind to a specification type or kind.
typeExpr :: (HasLetSynonym m, TypeEnvMonad m) => RLType -> m Type.Type
typeExpr lty =
  case unLoc lty
  of VarT v -> do
       -- Look up this type, if it's a @let type@ synonym
       mtype <- lookupLetTypeSynonym v
       case mtype of 
         Just t -> return t
         Nothing -> return $ Type.VarT (toVar v)
     IntIndexT n -> return $ Type.IntT n
     TupleT tuple_args -> do
       -- Get types and kinds of type arguments
       types_kinds <- mapM typeAndKind tuple_args
       let (ts, ks) = unzip types_kinds
           get_kind k =
             case Type.toBaseKind k
             of Type.BoxK -> Type.BoxK
                Type.ValK -> Type.ValK
                _ -> internalError "typeExpr: Not a valid tuple field type"
       return $ Type.typeApp (Type.UTupleT $ map get_kind ks) ts
     AppT op arg ->
       Type.AppT `liftM` typeExpr op `ap` typeExpr arg
     FunT dom rng ->
       Type.FunT `liftM` typeExpr dom `ap` typeExpr rng
     AllT dom rng -> domain dom $ \dom' ->
       Type.AllT dom' `liftM` typeExpr rng
     LamT doms body ->
       -- Do one parameter at a type
       let mk_lambda (dom : doms) body =
             domain dom $ \dom' ->
             Type.LamT dom' `liftM` mk_lambda doms body
           mk_lambda [] body = typeExpr body
       in mk_lambda doms body
     CoT kind dom rng -> do
       kind' <- typeExpr kind
       dom' <- typeExpr dom
       rng' <- typeExpr rng
       return $ Type.typeApp (Type.CoT kind') [dom', rng']

translateDataConDecl :: Var -> DataConDecl Resolved -> TransT DataConDescr
translateDataConDecl data_type_con decl =
  domains (dconExTypes decl) $ \ex_types -> do
    args_and_kinds <- mapM typeAndKind $ dconArgs decl
    let fields = [(t, Type.toBaseKind k) | (t, k) <- args_and_kinds]
        dcon_var = toVar $ dconVar decl
    return (DataConDescr dcon_var ex_types fields)

varEnt :: Var -> LType Resolved -> [Attribute] -> TransT UpdateTypeEnv
varEnt ident ty attrs = do
  let conlike = fromVarAttrs attrs
  ty' <- typeExpr ty
  let update = UpdateTypeEnv (insertTypeWithProperties ident ty' conlike)
  return $! conlike `seq` update

typeEnt ident ty = do
  ty' <- typeExpr ty

  -- Look up the type function by its name
  let name = case varName ident
             of Just l -> labelLocalNameAsString l
  type_function <- lookupBuiltinTypeFunction name
  return $ UpdateTypeEnv
    (maybe (insertType ident ty') (insertTypeFunction ident ty') type_function)

dataEnt core_name dom ty data_cons attrs = do
  kind <- typeExpr ty
  let abstract = AbstractAttr `elem` attrs
      algebraic = not $ NonalgebraicAttr `elem` attrs

  domains dom $ \params -> do
    data_con_descrs <-
      mapM (translateDataConDecl core_name . unLoc) data_cons
    let descr = DataTypeDescr core_name params (Type.toBaseKind kind) data_con_descrs abstract algebraic
    return $ UpdateTypeEnv (insertDataType descr)

-- | Translate a global type-related declaration.
typeLevelDecl :: LDecl Resolved -> TransT UpdateTypeEnv
typeLevelDecl ldecl = do 
  let Decl ident ent = unLoc ldecl
      core_name = toVar ident
  case ent of
    VarEnt ty attrs ->
      varEnt core_name ty attrs
    TypeEnt ty ->
      typeEnt core_name ty
    DataEnt dom ty data_cons attrs ->
      dataEnt core_name dom ty data_cons attrs

    -- Translate only the types of functions and constants
    FunEnt (L pos f) attrs ->
      varEnt core_name (funType pos showResolvedVar f) attrs
    ConstEnt ty _ attrs ->
      varEnt core_name ty attrs

-- | Create a type environment from the given declarations
declTypeEnvironment :: [LDecl Resolved] -> TransT UpdateTypeEnv
declTypeEnvironment decls = liftM mconcat $ mapM typeLevelDecl decls

-------------------------------------------------------------------------------
-- Third-pass type translation. 
--
-- Translate global expressions and constants.
-- Type functions must be evaluated in this phase, so we provide
-- a Mem type environment.

data TransEEnv = TransEEnv (IdentSupply Var) LetTypeEnv TypeEnv

newtype TransE a = TransE (ReaderT TransEEnv IO a)

instance Monad TransE where
  return x = TransE (return x)
  TransE m >>= k = TransE (m >>= \x -> case k x of TransE m' -> m')

instance TypeEnvMonad TransE where
  type TypeFunctionInfo TransE = TypeFunction
  getTypeEnv = TransE (asks $ \(TransEEnv _ _ e) -> e)
  askTypeEnv f = TransE (asks $ \(TransEEnv _ _ e) -> f e)

  assumeWithProperties v t b (TransE m) = TransE (local insert m)
    where
      insert (TransEEnv s l env) =
        TransEEnv s l (insertTypeWithProperties v t b env)

instance MonadIO TransE where
  liftIO m = TransE (liftIO m)

instance Supplies TransE (Ident Var) where
  fresh = TransE $ ReaderT $ \(TransEEnv s _ _) -> supplyValue s

instance EvalMonad TransE where
  liftTypeEvalM m = TransE $ ReaderT $ \(TransEEnv s _ e) ->
    runTypeEvalM m s e

instance HasLetSynonym TransE where
  lookupLetTypeSynonym rv =
    TransE $ asks (\(TransEEnv _ m _) -> Map.lookup (toVar rv) m)

  withLetTypeSynonym v t (TransE m) =
    TransE $ local (\(TransEEnv s m env) -> TransEEnv s (Map.insert (toVar v) t m) env) m

runExprTranslation :: IdentSupply Var
                   -> [(Var, Type.Type)] -- ^ Let type synonyms
                   -> TypeEnv            -- ^ Starting type environment
                   -> TransE a           -- ^ Computation to run
                   -> IO a
runExprTranslation s type_synonyms tenv (TransE m) =
  let let_types = Map.fromList type_synonyms
      env = TransEEnv s Map.empty tenv
  in runReaderT m env

-- | Convert function definition attributes
defAttributes :: [Attribute] -> (SystemF.DefAnn -> SystemF.DefAnn)
defAttributes attrs ann =
  case check_attrs 
  of () -> foldr insert_attribute ann attrs
  where
    -- Verify that the attribute list doesn't contain conflicting
    -- attributes; throw an exception on error.
    -- Invalid attributes are checked when inserting.
    check_attrs = check_inlining_attrs

    -- There should be at most one inlining phase attribute
    check_inlining_attrs =
      case filter (`elem` [InlineSequentialAttr, InlineDimensionalityAttr, InlineFinalAttr, InlinePostfinalAttr]) attrs
      of []  -> ()
         [_] -> ()
         _   -> internalError "Functions may not have more than one inlining phase attribute"

    insert_attribute InlineAttr ann =
      ann {SystemF.defAnnInlineRequest = True}

    -- TODO: This attribute is specified in two places: the type declaration, 
    -- and here.  Eliminate this one and take the attribute from the type.
    insert_attribute ConlikeAttr ann =
      ann {SystemF.defAnnConlike = True}

    insert_attribute InlineDimensionalityAttr ann =
      ann {SystemF.defAnnInlinePhase = SystemF.InlDimensionality}

    insert_attribute InlineSequentialAttr ann =
      ann {SystemF.defAnnInlinePhase = SystemF.InlSequential}
    
    insert_attribute InlineFinalAttr ann =
      ann {SystemF.defAnnInlinePhase = SystemF.InlFinal}

    insert_attribute InlinePostfinalAttr ann =
      ann {SystemF.defAnnInlinePhase = SystemF.InlPostfinal}

    insert_attribute _ _ =
      internalError "Unexpected function attribute"

-- | Update the annotations on a 'SystemF.Def'.  Attributes are converted
--   to properties of the annotation.
--   If functions are is labeled as exported.
applyDefAttributes :: Bool
                   -> [Attribute]
                   -> SystemF.Def t SystemF.Mem
                   -> SystemF.Def t SystemF.Mem
applyDefAttributes is_global attrs def = SystemF.modifyDefAnnotation f def 
  where
    -- Global functions are exported.  Local functions are not.
    is_exported = is_global

    f annotation =
      defAttributes attrs $ annotation {SystemF.defAnnExported = is_exported}

assumeDefGroup :: [LDef Resolved] -> TransE a -> TransE a
assumeDefGroup defs m = do
  -- Add function types to environment
  let vars = [toVar $ dName d | L _ d <- defs]
  fun_types <- sequence [typeInExp $ funType pos showResolvedVar (dFun d)
                        | L pos d <- defs]
  assumeBinders (zipWith (:::) vars fun_types) m

-- | Translate a domain that must have an explicit type.
--   Convert to mem types.
domainInExp :: Domain Resolved -> (Type.Binder -> TransE a) -> TransE a
domainInExp (Domain param (Just ty)) k = do
  let v = toVar param
  t <- typeInExp ty
  assume v t $ k (v ::: t)

domainInExp (Domain _ Nothing) _ =
  -- This error should have been caught during parsing
  internalError "domain: Missing type annotation"

-- | Translate a list of domains that must have explicit types
domainsInExp :: [Domain Resolved] -> ([Type.Binder] -> TransE a) -> TransE a
domainsInExp = withMany domainInExp

-- | Translate a domain that must have an explicit type
optDomainInExp :: SourcePos -> Type.Type -> Domain Resolved
               -> (Type.Binder -> TransE a)
               -> TransE a
optDomainInExp pos given_type (Domain param Nothing) k = do
  -- Use given type
  let v = toVar param
  assume v given_type $ k (v ::: given_type)

optDomainInExp pos given_type (Domain param (Just ty)) k = do
  -- Verify that types match
  annotated_ty <- typeInExp ty
  match <- Type.Compare.compareTypes annotated_ty given_type
  unless match $
    let err = SystemF.Typecheck.genericTypeMismatch pos (Type.getLevel given_type)
              given_type annotated_ty
    in SystemF.Typecheck.typeError err

  let v = toVar param
  assume v given_type $ k (v ::: given_type)

-- | Translate a list of domains with optional type annotations.
--   The types of the bound variables are given to this function.
--   If the domain has a type annotation, it's compared to the given type.
optDomainsInExp :: SourcePos -> [Type.Type] -> [Domain Resolved]
                -> ([Type.Binder] -> TransE a)
                -> TransE a
optDomainsInExp pos tys domains k 
  | length tys /= length domains =
      error "Wrong number of bound variables"
  | otherwise = withMany (uncurry (optDomainInExp pos)) (zip tys domains) k

-- | Generate code of a type appearing in an expression.
--   'Init' terms are expanded so that type checking can proceed.
typeInExp :: RLType -> TransE Type.Type
typeInExp t = expandType `liftM` typeExpr t

-- | Translate an AST type to a specification type and compute its kind.
typeKindInExp :: RLType -> TransE (Type.Type, Type.Kind)
typeKindInExp lty = do
  ty <- typeInExp lty
  k <- typeKind ty
  return (ty, k)

exprs :: [RLExp] -> TransE ([SystemF.ExpM], [Type.Type])
exprs = mapAndUnzipM expr

-- | Translate an AST expression to a System F expression and compute its type.
--
--   Some translations require System F type information, which is looked up
--   as needed.
expr :: RLExp -> TransE (SystemF.ExpM, Type.Type)
expr (L pos expression) =
  case expression
  of VarE v -> do
       -- Translate to either a data constructor or a variable
       tenv <- getTypeEnv
       case lookupDataConWithType (toVar v) tenv of
         Just (type_con, data_con) ->
           translateCon inf type_con data_con (toVar v) [] []
         Nothing -> do
           let v' = toVar v
           ty <- liftTypeEvalM $ SystemF.TypecheckMem.tcVar pos v'
           return (SystemF.varE inf v', ty)
     IntE n ->
       let e = SystemF.ExpM $ SystemF.LitE inf (SystemF.IntL n int_type)
       in return (e, int_type)
     FloatE n ->
       let e = SystemF.ExpM $ SystemF.LitE inf (SystemF.FloatL n float_type)
       in return (e, float_type)
     TupleE es -> do
       (es', types) <- exprs es
       tenv <- getTypeEnv
       let kinds = [Type.toBaseKind $ Type.Eval.typeKind tenv t | t <- types]
       let con = SystemF.TupleCon types
           tuple_type = Type.UTupleT kinds `Type.typeApp` types
       return (SystemF.ExpM $ SystemF.ConE inf con es', tuple_type)
     TAppE op arg ->
       let (op', args) = uncurryTypeApp op [arg]
       in translateApp inf op' args []
     AppE op arg ->
       let (op', ty_args, args) = uncurryApp op [arg]
       in translateApp inf op' ty_args args
     LamE f -> do
       f' <- translateFun pos f
       return (SystemF.ExpM $ SystemF.LamE inf f', SystemF.functionType f')
     CaseE s alts -> do
       (s', scrutinee_type) <- expr s

       -- Compute the type being scrutinized for local type inference
       whnf_scrutinee_type <- Type.Eval.reduceToWhnf scrutinee_type
       let (s_ty_op, s_ty_args) = Type.fromTypeApp whnf_scrutinee_type

       -- Infer alternatives
       (alts', alt_types) <-
         mapAndUnzipM (translateLAlt s_ty_op s_ty_args) alts
       let ty = case alt_types of t:_ -> t
       return (SystemF.ExpM $ SystemF.CaseE inf s' alts', ty)
     LetE binder rhs body -> do
       (rhs', rhs_type) <- expr rhs
       -- Use the inferred type of the RHS as the bound variable's type
       optDomainInExp pos rhs_type binder $ \binder' -> do
         (body', body_type) <- expr body
         let pattern = SystemF.patM binder'
             e = SystemF.ExpM $ SystemF.LetE inf pattern rhs' body'
         return (e, body_type)
     LetTypeE dom rhs body -> do
       -- Define a type synonym.
       -- No code is actually generated from this expression.
       ty <- typeInExp rhs
       withLetTypeSynonym dom ty $ expr body
     LetfunE defs body -> assumeDefGroup defs $ do
       functions <- sequence [translateFun pos (dFun d) | L pos d <- defs]
       let systemf_defs = [applyDefAttributes False (dAttributes d) $
                           SystemF.mkDef (toVar $ dName d) f
                          | (L _ d, f) <- zip defs functions]
       let defgroup = SystemF.Rec systemf_defs
       (body', body_type) <- expr body
       return (SystemF.ExpM $ SystemF.LetfunE inf defgroup body', body_type)
     ExceptE t -> do
       t' <- typeInExp t
       return (SystemF.ExpM $ SystemF.ExceptE inf t', t')
     CoerceE from_t to_t body -> do
       ft <- typeInExp from_t
       tt <- typeInExp to_t
       (body', _) <- expr body
       return (SystemF.ExpM $ SystemF.CoerceE inf ft tt body', tt)
  where
    int_type = Type.intT
    float_type = Type.floatT
    inf = SystemF.mkExpInfo pos

-- | Translate an application to an appropriate term.
--   It's either a function application or data constructor application.
translateApp inf op ty_args args = do
  -- Is the operator a data constructor?
  tenv <- getTypeEnv
  case unLoc op of
    VarE v
      | Just (type_con, data_con) <- lookupDataConWithType (toVar v) tenv ->
          translateCon inf type_con data_con (toVar v) ty_args args
    _ -> do
      -- Create an application term
      (op_exp, op_type) <- expr op
      translateAppWithOperator inf op_exp op_type ty_args args

translateAppWithOperator inf op_exp op_type ty_args args = do
  -- Examine arguments
  arg_types_and_kinds <- mapM typeKindInExp ty_args
  let arg_types = map fst arg_types_and_kinds
  let arg_kinds_and_types = [(k, t) | (t, k) <- arg_types_and_kinds]
  (arg_exps, arg_tys) <- exprs args

  -- Compute type of result
  result_type <- liftTypeEvalM $
                 SystemF.TypecheckMem.tcApp (getSourcePos inf)
                 op_type arg_kinds_and_types arg_tys
  let result = SystemF.ExpM $ SystemF.AppE inf op_exp arg_types arg_exps
  return (result, result_type)

translateCon :: SystemF.ExpInfo -> DataType -> DataConType
             -> Var -> [RLType] -> [RLExp] -> TransE (SystemF.ExpM, Type.Type)
translateCon inf type_con data_con op ty_args args
  | length ty_args /= n_ty_args + n_ex_types =
    error $ show (getSourcePos inf) ++ ": Wrong number of type arguments to data constructor"
  | length args < n_args =
    -- Instead of producing an error, the constructor could be eta-expanded.
    error $ show (getSourcePos inf) ++ ": Too few arguments to data constructor"
  | otherwise = do
      -- Convert type arguments
      arg_types <- mapM typeInExp ty_args
      let con_ty_args = take n_ty_args arg_types
          con_ex_args = drop n_ty_args arg_types

      -- Convert constructor arguments
      let con_args = take n_args args
          other_args = drop n_args args
      (con_args', con_arg_tys) <- exprs con_args
      let con = SystemF.VarCon op con_ty_args con_ex_args 
          con_exp = SystemF.ExpM $ SystemF.ConE inf con con_args'

      -- Compute type
      con_type <- liftTypeEvalM $
                  SystemF.TypecheckMem.tcCon (getSourcePos inf) con con_arg_tys

      -- If any arguments remain, apply them
      if null other_args
        then return (con_exp, con_type)
        else translateAppWithOperator inf con_exp con_type [] other_args
    
  where
    n_ty_args = length $ dataConTyParams data_con
    n_ex_types = length $ dataConExTypes data_con
    n_args = length $ dataConFields data_con


uncurryTypeApp e ty_args =
  case unLoc e
  of TAppE op arg -> uncurryTypeApp op (arg : ty_args)
     _ -> (e, ty_args)

uncurryApp e args =
  case unLoc e
  of AppE op arg -> uncurryApp op (arg : args)
     _ -> case uncurryTypeApp e []
          of (op, ty_args) -> (op, ty_args, args)

-- | Translate a case alternative.  The scrutinee has type
--   @typeApp s_ty_op s_ty_args@.
translateLAlt :: Type.Type -> [Type.Type] -> Located (Alt Resolved)
             -> TransE (SystemF.AltM, Type.Type)
translateLAlt s_ty_op s_ty_args (L pos (Alt pattern body)) =
  with_pattern pattern $ \new_con val_binders -> do
    (body', body_type) <- expr body
    let alt = SystemF.AltM $
              SystemF.Alt { SystemF.altCon = new_con
                          , SystemF.altParams = map SystemF.patM val_binders
                          , SystemF.altBody = body'}
    return (alt, body_type)
  where
    with_pattern (ConPattern con _ ex_types fields) k = do
      tenv <- getTypeEnv
      let Just dcon_type = lookupDataCon (toVar con) tenv

      -- Check that the operator is this data constructor's type constructor
      case s_ty_op of
        Type.VarT op_var | op_var == dataConTyCon dcon_type ->
          return ()
        _ -> error $ show pos ++ ": Case alternative's data constructor does not match scrutinee type"
      ty_args' <- return s_ty_args -- mapM typeInExp ty_args

      -- Infer types of other fields
      (ty_binders, field_types, _) <-
        Type.Eval.instantiateDataConType
        dcon_type ty_args' [toVar $ boundVar d | d <- ex_types]

      -- Compare with the annotated types
      let inferred_ex_kinds = map binderType ty_binders
      optDomainsInExp pos inferred_ex_kinds ex_types $ \ty_binders ->
        optDomainsInExp pos field_types fields $ \val_binders ->
          let new_con = SystemF.VarDeCon (toVar con) ty_args' ty_binders
          in k new_con val_binders

    with_pattern (TuplePattern fields) k =
      domainsInExp fields $ \val_binders ->
        let new_con = SystemF.TupleDeCon [t | _ ::: t <- val_binders]
        in k new_con val_binders

translateFun pos f =
  domainsInExp (fTyParams f) $ \ty_binders ->
  domainsInExp (fParams f) $ \val_binders -> do
    range <- typeInExp $ fRange f
    (body, _) <- expr $ fBody f
    return $ SystemF.FunM $
      SystemF.Fun { SystemF.funInfo = SystemF.mkExpInfo pos
                  , SystemF.funTyParams = map SystemF.TyPat ty_binders
                  , SystemF.funParams = map SystemF.patM val_binders
                  , SystemF.funReturn = range
                  , SystemF.funBody = body}

translateGlobalFun name pos f attrs = do
  f' <- translateFun pos f
  let fun_definition = SystemF.mkDef name $ SystemF.FunEnt f'
  return $ applyDefAttributes True attrs fun_definition

translateGlobalConstant name pos ty d attrs = do
  ty' <- typeInExp ty
  (value, _) <- expr d
  let constant = SystemF.Constant (SystemF.mkExpInfo pos) ty' value
      def = SystemF.mkDef name (SystemF.DataEnt constant)
  return $ applyDefAttributes True attrs def

declGlobalEntity (L pos decl) =
  case decl
  of Decl name ent ->
       case ent
       of FunEnt (L fun_pos f) attrs ->
            liftM Just $ translateGlobalFun (toVar name) fun_pos f attrs
          ConstEnt ty d attrs ->
            liftM Just $ translateGlobalConstant (toVar name) pos ty d attrs
          _ -> return Nothing

declGlobals decls = do
  m_defs <- mapM declGlobalEntity decls
  let defs = catMaybes m_defs
  return $ SystemF.Module builtinModuleName [] [SystemF.Rec defs] []

-------------------------------------------------------------------------------

-- | Get all global variables introduced by a declaration
lDeclVariables :: LDecl Resolved -> [ResolvedVar]
lDeclVariables (L _ (Decl ident ent)) = ident : subordinates
  where
    subordinates =
      case ent
      of DataEnt _ _ decls _ -> [dconVar d | L _ d <- decls]
         _ -> []

-- | Create a lookup table of variable names
variableNameTable :: [LDecl Resolved] -> VariableNameTable
variableNameTable decls = Map.fromList keyvals
  where
    keyvals = [(name, v) | decl <- decls
                         , ResolvedVar v <- lDeclVariables decl
                         , Just lab <- return $ varName v
                         , Left name <- return $ labelLocalName lab]

createCoreModule :: IdentSupply Var -> RModule
                 -> IO (TypeEnv, SpecTypeEnv, TypeEnv,
                        SystemF.Module SystemF.Mem, Map.Map String Var)
createCoreModule var_supply (Module decls) = do
  -- Create a table of variable names
  let name_table = variableNameTable decls
  let builtin_type_functions = builtinTypeFunctions name_table
      
  -- Create a type environment with kind information
  let kind_env_updates =
        runTypeTranslation wiredInTypeEnv builtin_type_functions $
        declKindEnvironment decls
      kind_env = applyUpdates kind_env_updates wiredInTypeEnv

  -- Create a type environment with type information.
  -- The kind environment is used while gathering type information.
  let type_env_updates =
        runTypeTranslation kind_env builtin_type_functions $
        declTypeEnvironment decls
      type_env = expandInitType $
                 applyUpdates type_env_updates wiredInTypeEnv

  -- Translate functions using this type environment
  let mem_env = toMemEnv type_env
  mem_module <- runExprTranslation var_supply [] mem_env $
                 declGlobals decls

  -- Construct final expressions and type environments
  let spec_env    = convertMemToSpec type_env
      sf_env      = convertSpecToSF name_table spec_env

  return (sf_env, spec_env, mem_env, mem_module, name_table)
