
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
import qualified SystemF.Syntax as SystemF
import qualified SystemF.MemoryIR as SystemF
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
       kinds <- mapM (toBaseKind pos . Type.Eval.typeKind tenv) types
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
    error $ show pos ++ ": Wrong number of type arguments to data constructor"
  | length args < n_args =
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

      -- Convert constructor arguments
      let con_args = take n_args args
          other_args = drop n_args args
      (con_args', con_arg_tys) <- exprs con_args
      let con = SystemF.VarCon op u_ty_args' e_ty_args'
          con_exp = SystemF.ExpM $ SystemF.ConE inf con con_args'

      -- Compute type
      con_type <- liftTypeEvalM $
                  SystemF.TypecheckMem.tcCon pos con con_arg_tys

      -- If any arguments remain, apply them
      if null other_args
        then return (con_exp, con_type)
        else translateAppWithOperator inf con_exp con_type [] other_args
    
  where
    pos = getSourcePos inf
    n_ty_args = length $ dataConTyParams data_con
    n_ex_types = length $ dataConExTypes data_con
    n_args = length $ dataConFields data_con

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
    with_pattern (ConPattern con ex_types fields) k = do
      tenv <- getTypeEnv
      -- 'con' must be a data constructor
      dcon_type <- case lookupDataCon (toVar con) tenv
                   of Nothing -> error $ show pos ++ ": Expecting a data constructor"
                      Just c  -> return c

      -- Check that the operator is this data constructor's type constructor
      case s_ty_op of
        Type.VarT op_var | op_var == dataConTyCon dcon_type ->
          return ()
        _ -> error $ show pos ++ ": Case alternative's data constructor does not match scrutinee type"
      ty_args' <- return s_ty_args

      -- Infer types of other fields
      when (length (dataConExTypes dcon_type) /= length ex_types) $
        error $ show pos ++ ": Wrong number of existential variables in pattern"
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
      optDomainsInExp pos s_ty_args fields $ \val_binders ->
        let new_con = SystemF.TupleDeCon [t | _ ::: t <- val_binders]
        in k new_con val_binders

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
                 -> IO (BoxedTypeEnv, TypeEnvBase SpecMode, TypeEnv,
                        SystemF.Module SystemF.Mem, Map.Map String Var)
createCoreModule var_supply mod@(Module decls) = do
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
  -- The kind environment is used while gathering type information.
  type_env <- typeTranslation var_supply type_subst kind_env builtin_type_functions mod

  -- Translate functions using this type environment
  let mem_env = type_env
  mem_module <- runExprTranslation var_supply type_subst builtin_type_functions mem_env $
                 declGlobals decls

  -- Construct final expressions and type environments
  let (spec_env, sf_env) = convertFromMemTypeEnv name_table type_env

  return (sf_env, spec_env, mem_env, mem_module, name_table)
