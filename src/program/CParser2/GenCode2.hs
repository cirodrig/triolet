
{-# LANGUAGE Rank2Types, GeneralizedNewtypeDeriving #-}
module CParser2.GenCode2 (createCoreModule) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map

import Common.MonadLogic
import Common.Identifier
import Common.SourcePos
import Common.Supply
import Common.Error
import Common.Label
import Builtins.TypeFunctions
import CParser2.AST
import CParser2.AdjustTypes
import qualified LowLevel.Syntax as LL
import SystemF.Datatypes.Driver
import qualified SystemF.Syntax as SystemF
import qualified SystemF.MemoryIR as SystemF
import SystemF.PrintMemoryIR
import qualified SystemF.SpecToMem as SystemF
import qualified SystemF.Typecheck
import qualified SystemF.TypecheckMem
import Type.Environment
import qualified Type.Error as Type
import qualified Type.Compare
import qualified Type.Eval
import Type.Var
import Type.Type(Binder(..), Level(..))
import qualified Type.Type as Type

import CParser2.GenCode.Util
import CParser2.GenCode.Kind
import CParser2.GenCode.Type

-- | Partition a list into sub-lists of the given lengths.
--   If the list is too short, return 'Nothing'.
--   If the list is too long, return the remaining items as another list.
segment :: [Int] -> [a] -> Maybe ([[a]], [a])
segment (n:ns) xs = do (xs1, xs') <- span_exact n xs
                       (xss, xs'') <- segment ns xs'
                       return (xs1 : xss, xs'')
  where
    span_exact n xs = go id n xs
      where
        go hd 0 xs     = return (hd [], xs)
        go hd n (x:xs) = go (hd . (x:)) (n-1) xs
        go _  _ []     = Nothing

segment [] xs = Just ([], xs)

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

type TransE = TransT

runExprTranslation s type_synonyms type_functions tenv m =
  runTypeTranslation s tenv type_synonyms type_functions m

-- | Convert function definition attributes
defAttributes :: [Attribute Resolved] -> (SystemF.DefAnn -> SystemF.DefAnn)
defAttributes attrs ann =
  case check_attrs 
  of () -> foldr insert_attribute ann attrs
  where
    -- Verify that the attribute list doesn't contain conflicting
    -- attributes; throw an exception on error.
    -- Invalid attributes are checked when inserting.
    check_attrs = check_inlining_phase `seq` check_inlining_eagerness

    -- There should be at most one inlining phase attribute
    check_inlining_phase =
      case filter (`elem` [InlineSequentialAttr, InlineFinalAttr, InlinePostfinalAttr]) attrs
      of []  -> ()
         [_] -> ()
         _   -> internalError "Functions may not have more than one inlining phase attribute"

    check_inlining_eagerness =
      case filter (`elem` [InlineAttr, InlineNeverAttr]) attrs
      of []  -> ()
         [_] -> ()
         _   -> internalError  "Functions may not have more than one inlining eagerness attribute"

    insert_attribute InlineAttr ann =
      ann {SystemF.defAnnInlineRequest = SystemF.InlAggressively}

    insert_attribute InlineNeverAttr ann =
      ann {SystemF.defAnnInlineRequest = SystemF.InlNever}

    -- TODO: This attribute is specified in two places: the type declaration, 
    -- and here.  Eliminate this one and take the attribute from the type.
    insert_attribute ConlikeAttr ann =
      ann {SystemF.defAnnConlike = True}

    insert_attribute InlineSequentialAttr ann =
      ann {SystemF.defAnnInlinePhase = SystemF.InlSequential}
    
    insert_attribute InlineFinalAttr ann =
      ann {SystemF.defAnnInlinePhase = SystemF.InlFinal}

    insert_attribute InlinePostfinalAttr ann =
      ann {SystemF.defAnnInlinePhase = SystemF.InlPostfinal}

    -- The 'builtin' attribute is only used during parsing
    insert_attribute BuiltinAttr ann =
      ann

    insert_attribute _ _ =
      internalError "Unexpected function attribute"

-- | Update the annotations on a 'SystemF.Def'.  Attributes are converted
--   to properties of the annotation.
--   If functions are is labeled as exported.
applyDefAttributes :: Bool
                   -> [Attribute Resolved]
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
domainInExp :: SourcePos -> Domain Resolved -> (Type.Binder -> TransE a)
            -> TransE a
domainInExp _ (Domain param (Just ty)) k = do
  let v = toVar param
  t <- typeInExp ty
  assume v t $ k (v ::: t)

domainInExp pos (Domain _ Nothing) _ =
  -- This error should have been caught during parsing
  internalError $ show pos ++ ": Missing type annotation in domain"

-- | Translate a list of domains that must have explicit types
domainsInExp :: SourcePos -> [Domain Resolved] -> ([Type.Binder] -> TransE a)
             -> TransE a
domainsInExp pos = withMany (domainInExp pos)

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
    let err = Type.genericTypeMismatch pos (Type.getLevel given_type)
              given_type annotated_ty
    in Type.throwTypeError err

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
--   Reduce the type as much as possible, to save work later on.
typeInExp :: RLType -> TransE Type.Type
typeInExp t = do
  (t', _) <- genType t
  Type.Eval.normalize t'

-- | Translate an AST type to a specification type and compute its kind.
--   Reduce the type as much as possible, to save work later on.
typeKindInExp :: RLType -> TransE (Type.Type, Type.Kind)
typeKindInExp t = do
  (t', k') <- genType t
  t'' <- Type.Eval.normalize t'
  return (t'', k')

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
       m_data_con <- lookupDataConWithType (toVar v)
       case m_data_con of
         Just (type_con, data_con) ->
           translateCon inf type_con data_con (toVar v) [] []
         Nothing ->
           variable_with_type $ toVar v
     IntE n ->
       let e = SystemF.ExpM $ SystemF.LitE inf (SystemF.IntL n int_type)
       in return (e, int_type)
     UIntE n ->
       let e = SystemF.ExpM $ SystemF.LitE inf (SystemF.IntL n uint_type)
       in return (e, uint_type)
     FloatE n ->
       let e = SystemF.ExpM $ SystemF.LitE inf (SystemF.FloatL n float_type)
       in return (e, float_type)
     TupleE es -> do
       (es', types) <- exprs es
       kinds <- mapM (toBaseKind pos <=< Type.Eval.typeKind) types
       let con = SystemF.TupleCon types
           tuple_type = Type.UTupleT kinds `Type.typeApp` types
       return (SystemF.ExpM $ SystemF.ConE inf con [] Nothing es', tuple_type)
     TAppE op arg ->
       let (op', args) = uncurryTypeApp op [arg]
       in translateApp inf op' args []
     AppE op arg ->
       let (op', ty_args, args) = uncurryApp op [arg]
       in translateApp inf op' ty_args args
     LamE f -> do
       f' <- translateFun pos f
       return (SystemF.ExpM $ SystemF.LamE inf f', SystemF.functionType f')
     CaseE s sps alts -> do
       (s', scrutinee_type) <- expr s
       (sps', sps_types) <- exprs sps

       -- Infer alternatives
       (alts', alt_types) <- mapAndUnzipM (translateLAlt scrutinee_type) alts

       -- Verify that all alternatives have the same type
       let ty:other_tys = alt_types
       liftTypeEvalM $ sequence_
         [ SystemF.Typecheck.checkType
           (Type.inconsistentCaseAlternatives pos i) ty t
         | (t, i) <- zip other_tys [2..]]
       return (SystemF.ExpM $ SystemF.CaseE inf s' sps' alts', ty)
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

     -- Resolve info variables to simple variables
     BoxedInfoE data_con -> do
       let con = toVar data_con
       m_datatype <- lookupDataConWithType con
       data_type <- case m_datatype
                    of Just (data_type, _) -> return data_type
                       Nothing -> error $ "Not a data constructor: " ++ show con
       variable_with_type $ dataTypeBoxedInfoVar data_type con
     UnboxedInfoE type_con -> do
       m_datatype <- lookupDataType (toVar type_con)
       data_type <- case m_datatype
                    of Just data_type -> return data_type
                       Nothing -> error $ "Not a type constructor: " ++ show (toVar type_con)
       variable_with_type $ dataTypeUnboxedInfoVar data_type
  where
    int_type = Type.intT
    uint_type = Type.uintT
    float_type = Type.floatT
    inf = SystemF.mkExpInfo pos

    variable_with_type v = do
      ty <- liftTypeEvalM $ SystemF.TypecheckMem.tcVar pos v
      return (SystemF.varE inf v, ty)

-- | Translate an application to an appropriate term.
--   It's either a function application or data constructor application.
translateApp inf op ty_args args = do
  -- Is the operator a data constructor?
  cond (unLoc op)
    [ do VarE v <- it
         Just (type_con, data_con) <- lift $ lookupDataConWithType (toVar v)
         lift $ translateCon inf type_con data_con (toVar v) ty_args args

    , lift $ do
         -- Create an application term
         (op_exp, op_type) <- expr op
         translateAppWithOperator inf op_exp op_type ty_args args
    ]

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
    error $ show pos ++ ": Wrong number of type arguments to data constructor"
  | length args < n_total_args =
    -- Instead of producing an error, the constructor could be eta-expanded.
    error $ show pos ++ ": Too few arguments to data constructor"
  | otherwise = do
      -- Convert type arguments
      let u_ty_args = take n_ty_args ty_args
          e_ty_args = drop n_ty_args ty_args
      (u_ty_args', u_kinds) <- mapAndUnzipM typeKindInExp u_ty_args
      sequence_ $ zipWith3 check_kind
                  [1..] (map binderType $ dataConTyParams data_con) u_kinds
      
      (e_ty_args', e_kinds) <- mapAndUnzipM typeKindInExp e_ty_args
      sequence_ $ zipWith3 check_kind
                  [n_ty_args + 1..] (map binderType $ dataConExTypes data_con) e_kinds

      -- Convert size parameters, type object, and constructor arguments
      let Just ([size_params, ty_ob, con_args], other_args) =
            segment [n_size_params, n_ty_objects, n_fields] args

      (size_params', size_param_tys) <- exprs size_params
      (ty_ob', ty_ob_ty) <- case ty_ob
                            of [] -> return (Nothing, Nothing)
                               [x] -> do (e, t) <- expr x
                                         return (Just e, Just t)
      (con_args', con_arg_tys) <- exprs con_args
      let con = SystemF.VarCon op u_ty_args' e_ty_args'
          con_exp = SystemF.ExpM $ SystemF.ConE inf con size_params' ty_ob' con_args'

      -- Compute type
      con_type <- liftTypeEvalM $
                  SystemF.TypecheckMem.tcCon pos con size_param_tys ty_ob_ty con_arg_tys

      -- If any arguments remain, apply them
      if null other_args
        then return (con_exp, con_type)
        else translateAppWithOperator inf con_exp con_type [] other_args
    
  where
    pos = getSourcePos inf
    n_ty_args = length $ dataConTyParams data_con
    n_ex_types = length $ dataConExTypes data_con
    n_size_params = length $ layoutSizeParamTypes $ dataTypeLayout' type_con
    n_ty_objects = case dataTypeKind type_con of {Type.BoxK -> 1; _ -> 0}
    n_fields = length $ dataConFields data_con
    n_total_args = n_size_params + n_ty_objects + n_fields

    -- Check the kind of a type parameter of the constructor
    check_kind i expected given = do
      eq <- Type.Compare.compareTypes expected given
      if eq
        then return ()
        else Type.throwTypeError $ Type.typeArgKindMismatch pos i expected given

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
--   The pattern must not have size arguments
translateLAlt :: Type.Type -> Located (Alt Resolved)
             -> TransE (SystemF.AltM, Type.Type)
translateLAlt s_ty (L pos (Alt pattern body))
  | null $ altSizeArgs pattern =
      withPattern pos s_ty pattern $ expr body
  | otherwise =
      error $ show pos ++ ": Size arguments not allowed in top-level patterns"

buildAlt pos new_con tyob_binder val_binders body =
  SystemF.AltM $
  SystemF.Alt { SystemF.altCon = new_con
              , SystemF.altTyObject = tyob_binder
              , SystemF.altParams = val_binders
              , SystemF.altBody = body}

-- | Instantiate a data constructor to match the given type.
--   Similar to 'instantiateDataConType', but reports detailed errors 
--   to users.
instantiateCon :: SourcePos
               -> Type.Var            -- ^ Data constructor
               -> Type.Type           -- ^ Type to instantiate to
               -> [Type.Var]          -- ^ Existentially bound variables
               -> Int                 -- ^ Number of given fields
               -> TransE (DataType, DataConType, [Type.Type],
                          [Type.Binder], Maybe Type.Type, [Type.Type])
instantiateCon pos con inst_type ex_vars n_binders = do
  -- Type must be a data constructor application
  decon_type <- liftTypeEvalM $ Type.Eval.deconVarAppType inst_type
  (tycon, ty_args) <-
    case decon_type
    of Just x  -> return x
       Nothing -> error $ show pos ++ ": Type is not a type application"

  -- 'con' must be a data constructor
  dcon_type <- do
    x <- lookupDataCon con
    case x of
      Nothing -> error $ show pos ++ ": Expecting a data constructor"
      Just c  -> return c
  let data_type = dataConType dcon_type
      is_boxed = dataTypeKind data_type == Type.BoxK

  -- Check that the operator is this data constructor's type constructor
  unless (tycon == dataConTyCon dcon_type) $
    error $ show pos ++ ": Case alternative's data constructor does not match scrutinee type"

  -- Check parameter list lengths
  let n_expected_type_binders = length (dataConExTypes dcon_type)
      n_fields = length $ dataConFields dcon_type
      n_expected_binders = n_fields + if is_boxed then 1 else 0

  when (n_expected_type_binders /= length ex_vars) $
    error $ show pos ++ ": Expecting " ++ show n_expected_type_binders ++ " Wrong number of existential variables in pattern"

  when (n_expected_binders /= n_binders) $
    error $ show pos ++ ": Expecting " ++ show n_expected_binders ++ " value binders"
  
  -- Infer types
  (ty_binders, field_types, _) <-
    Type.Eval.instantiateDataConType dcon_type ty_args ex_vars
  tyob_type <-
    if is_boxed
    then liftM Just $ Type.Eval.instantiateInfoType data_type ty_args
    else return Nothing

  return (data_type, dcon_type, ty_args, ty_binders, tyob_type, field_types)

withPattern :: SourcePos -> Type.Type -> Pattern Resolved
            -> TransE (SystemF.ExpM, a)
            -> TransE (SystemF.AltM, a)
withPattern pos scrutinee_type (ConPattern _ con ex_types binders) do_body = do

  -- Instantiate the constructor at the scrutinee type;
  -- verify length of given parameter lists
  (data_type, dcon_type, ty_args, ty_binders, tyob_type, field_types) <-
    instantiateCon pos (toVar con) scrutinee_type
    [toVar $ boundVar d | d <- ex_types] (length binders)

  let is_boxed = dataTypeKind data_type == Type.BoxK
  let inferred_ex_kinds = map binderType ty_binders
      inferred_ex_types = map (Type.VarT . binderVar) ty_binders

  -- Associate the given binders with the inferred types
  let tyob_type_binder :: Maybe (Type.Type, Pattern Resolved)
      other_binders :: [(Type.Type, Pattern Resolved)]
      (tyob_type_binder, other_binders) =
        case tyob_type
        of Nothing -> (Nothing, zip field_types binders)
           Just t  ->
             case binders
             of (b:bs) -> (Just (t, b), zip field_types bs)
                [] -> error $ show pos ++ ": Missing a type object binder"

  -- Compare with the annotated kinds
  optDomainsInExp pos inferred_ex_kinds ex_types $ \ty_binders -> do

    (body', (tyob_pattern, (patterns, x))) <-
      bindPatternMaybe pos tyob_type_binder $
      bindPatternList pos other_binders do_body

    -- Construct case alternative
    let new_con = SystemF.VarDeCon (toVar con) ty_args ty_binders
    return (buildAlt pos new_con tyob_pattern patterns body', x)

withPattern pos scrutinee_type (TuplePattern fields) do_body = do
  -- Compute the type being scrutinized for local type inference
  whnf_scrutinee_type <- Type.Eval.reduceToWhnf scrutinee_type
  let (s_ty_op, field_types) = Type.fromTypeApp whnf_scrutinee_type

  (body', (patterns, x)) <-
    bindPatternList pos (zip field_types fields) do_body

  let new_con = SystemF.TupleDeCon $ map SystemF.patMType patterns
  return (buildAlt pos new_con Nothing patterns body', x)

-- | Bind multiple patterns over the scope of an expression.
--   Return the translated expression and the patterns' variable bindings.
bindPatternList :: SourcePos
                -> [(Type.Type, Pattern Resolved)]
                -> TransE (SystemF.ExpM, a)
                -> TransE (SystemF.ExpM, ([SystemF.PatM], a))
bindPatternList pos ps m = go ps 
  where
    go ((ty, pat):ps) = do
      (p', (e, (ps', t))) <- bindPattern pos ty pat $ go ps
      return (e, (p' : ps', t))

    go [] = do
      (e, t) <- m
      return (e, ([], t))

bindPatternMaybe :: SourcePos
                 -> Maybe (Type.Type, Pattern Resolved)
                 -> TransE (SystemF.ExpM, a)
                 -> TransE (SystemF.ExpM, (Maybe SystemF.PatM, a))
bindPatternMaybe pos Nothing m = do
  (e, x) <- m
  return (e, (Nothing, x))
  
bindPatternMaybe pos (Just (ty, pat)) m = do
  (p', (e, x)) <- bindPattern pos ty pat m
  return (e, (Just p', x))

bindPattern :: SourcePos -> Type.Type -> Pattern Resolved
            -> TransE (SystemF.ExpM, a)
            -> TransE (SystemF.PatM, (SystemF.ExpM, a))
bindPattern pos ty pat m =
  case pat
  of VarPattern dom ->
       -- Bind this simple pattern
       optDomainInExp pos ty dom $ \b -> do
         x <- m
         return (SystemF.patM b, x)

     ConOrVarPattern {} ->
       internalError "bindPattern"

     _ -> do
       -- Create a case alternative to deconstruct this complex pattern
       (alt, x) <- withPattern pos ty pat m

       -- Get the size arguments from the pattern, and put them into the
       -- case expression
       (sps, _) <- exprs $ altSizeArgs pat

       -- Create a temporary variable to hold the scrutinee
       pattern_var <- newAnonymousVar ObjectLevel

       let pattern = SystemF.patM (pattern_var ::: ty)
           scrutinee = SystemF.ExpM $
                       SystemF.VarE (SystemF.mkExpInfo pos) pattern_var
           expr = SystemF.ExpM $
                  SystemF.CaseE (SystemF.mkExpInfo pos) scrutinee sps [alt]
       return (pattern, (expr, x))

translateFun pos f =
  domainsInExp pos (fTyParams f) $ \ty_binders ->
  domainsInExp pos (fParams f) $ \val_binders -> do
    range <- typeInExp $ fRange f
    (body, body_type) <- expr $ fBody f

    -- Check return type
    return_type_match <- Type.Compare.compareTypes range body_type
    unless return_type_match $
      Type.throwTypeError $ Type.returnTypeMismatch pos range body_type

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

declGlobalEntity var _ (FunEnt (L fun_pos f) attrs) =
  liftM Just $ translateGlobalFun var fun_pos f attrs

declGlobalEntity var pos (ConstEnt ty d attrs) =
  liftM Just $ translateGlobalConstant var pos ty d attrs

declGlobalEntity _ _ _ =
  return Nothing

declGlobalEntities :: [RLDecl] -> TransT [Maybe (SystemF.Def SystemF.Ent SystemF.Mem)]
declGlobalEntities (L pos decl : ldecls) =
  case decl
  of Decl name ent ->
       case ent
       of TypeSynEnt ty -> do
            -- Expand the type synonym
            ty' <- typeInExp ty
            withLetTypeSynonym name ty' $ declGlobalEntities ldecls

          _ -> do
            -- Process this entity and generate a global thing
            x <- declGlobalEntity (toVar name) pos ent

            -- Process other entities
            liftM (x:) $ declGlobalEntities ldecls

declGlobalEntities [] = return []

declGlobals decls = do
  m_defs <- declGlobalEntities decls
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

createCoreModule :: IdentSupply LL.Var -> IdentSupply Var -> RModule
                 -> IO (ITypeEnvBase FullyBoxedMode,
                        ITypeEnvBase SpecMode,
                        ITypeEnvBase UnboxedMode,
                        SystemF.Module SystemF.Mem,
                        Map.Map String Var)
createCoreModule ll_var_supply var_supply mod@(Module decls) = do
  -- Create a table of variable names
  let name_table = variableNameTable decls
  let builtin_type_functions = builtinTypeFunctions name_table

  -- Treat 'Init' as a shorthand for a function type
  init_param <- do var_id <- supplyValue var_supply
                   return $ mkAnonymousVar var_id TypeLevel
  let init_type = Type.LamT
                  (init_param Type.::: Type.bareT)
                  (Type.FunT (Type.AppT Type.outPtrT (Type.VarT init_param))
                   Type.storeT)
  let type_subst = [(Type.initV, Type.boxT),
                    (Type.initConV, init_type)]
      
  -- Create a type environment with kind information
  kind_env <- kindTranslation var_supply type_subst builtin_type_functions mod

  -- Create a type environment with type information.
  -- The kind environment is used while gathering type information, but is
  -- not part of the final type environment.
  -- Type constructors' info variables are annotated onto the type
  -- constructors at this point.
  type_env <- typeTranslation var_supply type_subst kind_env builtin_type_functions mod

  -- Compute size parameters in this type environment, updating 'type_env'
  (updated_types, type_info_defs) <-
    computeDataTypeInfo ll_var_supply var_supply type_env

  -- DEBUG
  --putStrLn "Type info definitions"
  --liftIO $ mapM_ (print . pprGDef) type_info_defs

  -- Add size parameters to the type environment
  addLayoutVariablesToTypeEnvironment updated_types type_env

{-let type_info_types = [(v, SystemF.entityType ens)
                        | SystemF.Def v _ ens <- type_info_defs]
  forM_ type_info_types $ \(v, t) -> insertGlobalType type_env v t-}

  -- Translate functions using this type environment
  mem_env <- runTypeEnvM type_env freezeTypeEnv :: IO (ITypeEnvBase UnboxedMode)
  mem_module <- do
    m <- runExprTranslation var_supply type_subst builtin_type_functions type_env $
         declGlobals decls

    -- Add generated definitions to the module
    let new_defs = case SystemF.modDefs m
                   of [SystemF.Rec ds] ->
                        [SystemF.Rec (type_info_defs ++ ds)]
    return $ m {SystemF.modDefs = new_defs}

  -- DEBUG
  {-putStrLn "Parsed module"
  print $ pprModule mem_module
  liftIO $ print $ pprTypeEnv mem_env-}

  -- Construct final expressions and type environments
  (spec_env, sf_env) <- convertFromMemTypeEnv name_table mem_env

  return (sf_env, spec_env, mem_env, mem_module, name_table)
