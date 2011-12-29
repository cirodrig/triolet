
{-# LANGUAGE Rank2Types #-}
module CParser2.GenCode (createCoreFunctions) where

import Control.Monad
import Control.Monad.Reader

import Common.SourcePos
import Common.Error
import Common.Label
import Builtins.Builtins
import CParser2.AST
import qualified Data.Map as Map
import qualified SystemF.Syntax as SystemF
import qualified SystemF.MemoryIR as SystemF
import qualified SystemF.TypecheckMem
import Type.Environment
import qualified Type.Compare
import qualified Type.Eval
import Type.Var
import Type.Type(Binder(..), Level(..))
import qualified Type.Type as Type

-- | Extract function declarations from a module
checkModule :: Module Resolved -> Module Resolved
checkModule mod@(Module decls) 
  | any (not . is_value_decl) decls =
      internalError "Expecting function declarations only"
  | otherwise = mod
  where
    is_value_decl ldecl =
      case unLoc ldecl
      of Decl _ (FunEnt {})   -> True
         Decl _ (ConstEnt {}) -> True
         _                    -> False

-- | During translation, keep a mapping from "let type"-bound identifiers
--   to types.  If a type is found in the mapping, it's replaced by its
--   assigned value.
type TransM a = ReaderT (Map.Map ResolvedVar Type.Type) TypeEvalM a

lookupLetTypeSynonym :: ResolvedVar -> TransM (Maybe Type.Type)
lookupLetTypeSynonym rv = asks (Map.lookup rv)

withLetTypeSynonym :: ResolvedVar -> Type.Type -> TransM a -> TransM a
withLetTypeSynonym v t = local (Map.insert v t)

liftT :: (forall a. TypeEvalM a -> TypeEvalM a) -> TransM a -> TransM a
liftT t (ReaderT f) = ReaderT (\x -> t (f x))

-------------------------------------------------------------------------------

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
      case filter (`elem` [InlineSequentialAttr, InlineDimensionalityAttr, InlineFinalAttr]) attrs
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

-- | Determine the type of an expression.
expType :: RLExp -> TransM Type.Type
expType (L pos expression) =
  case expression
  of VarE v -> do
       Just ty <- lift $ askTypeEnv (lookupType (toVar v))
       return ty
     IntE _ -> return $ Type.VarT $ pyonBuiltin The_int
     TAppE op arg -> do
       -- Compute the result of type application
       op_type <- expType op
       arg' <- translateType arg
       tenv <- lift getTypeEnv
       let arg_kind = Type.Eval.typeKind tenv arg'
       Just rt <- lift $ Type.Eval.typeOfTypeApp op_type arg_kind arg'
       return rt
     AppE op arg -> do
       -- Compute the applied type
       op_type <- expType op
       arg_type <- expType arg
       Just rt <- lift $ Type.Eval.typeOfApp op_type arg_type
       return rt
     LamE f -> translateType $ funType pos f
     CaseE _ (L _ alt:_) -> do
       ty_binders <- mapM translateDomain $ altExTypes (altPattern alt)
       liftT (assumeBinders ty_binders) $ do
         val_binders <- mapM translateDomain $ altFields (altPattern alt)
         liftT (assumeBinders val_binders) $ do
           expType (altBody alt)
     LetE dom _ body -> do
       binder <- translateDomain dom
       liftT (assumeBinder binder) $ expType body
     LetTypeE dom rhs body -> do
       typ <- translateType rhs
       withLetTypeSynonym dom typ $ expType body
     LetfunE defs body -> do
       assumeDefGroup defs $ expType body
     ExceptE t -> translateType t

expKind :: RLExp -> TransM Type.Kind
expKind e = do
  t <- expType e
  tenv <- lift getTypeEnv
  return $ Type.Eval.typeKind tenv t

typeKind :: RType -> TransM Type.Kind
typeKind t =
  case t
  of VarT v -> do
       Just k <- lift $ askTypeEnv (lookupType (toVar v))
       return k
     IntIndexT n -> return $ Type.intindexT
     TupleT _ ->
       -- Unboxed tuples have value kind
       -- The tuple type is not checked for validity.  The type will be
       -- checked when it's translated.
       return $ Type.valT
     AppT op _ -> do
       op_k <- typeKind $ unLoc op
       return $! case op_k
                 of Type.FunT _ rng -> rng
                    _ -> internalError "typeKind: Not a function type"
     FunT _ _ -> return Type.boxT
     AllT (Domain v dom) rng -> do
       dom' <- translateType dom
       liftT (assume (toVar v) dom') $ typeKind $ unLoc rng

assumeDefGroup :: [LDef Resolved] -> TransM b -> TransM b
assumeDefGroup defs m = do
  -- Add function types to environment
  let vars = [toVar $ dName d | L _ d <- defs]
  fun_types <- sequence [translateType $ funType pos (dFun d)
                        | L pos d <- defs]
  liftT (assumeBinders (zipWith (:::) vars fun_types)) m

-------------------------------------------------------------------------------

toVar (ResolvedVar v _) = v

translateDomain :: Domain Resolved -> TransM Type.Binder
translateDomain (Domain param ty) =
  liftM (toVar param :::) $ translateType ty

-- | Translate an AST type to a 'mem' type.
--   First the type is translated to a 'spec' type, then 
--   it's converted to 'mem'.
translateType :: RLType -> TransM Type.Type
translateType t = liftM specToMemType $ translateType' t

-- | Translate an AST type to a specification type.  This function is
--   only used by 'translateType'.
translateType' :: RLType -> TransM Type.Type
translateType' lty =
  case unLoc lty
  of VarT v -> do
       -- Look up this type, if it's a @let type@ synonym
       mtype <- lookupLetTypeSynonym v
       case mtype of 
         Just t -> return t
         Nothing -> return $ Type.VarT (toVar v)
     IntIndexT n -> return $ Type.IntT n
     TupleT tuple_args -> do
       -- Get kinds of type arguments
       tenv <- lift getTypeEnv
       tys <- mapM translateType' tuple_args
       let kinds = map get_kind tys
             where
               get_kind t =
                 case Type.toBaseKind $ Type.Eval.typeKind tenv t
                 of Type.BoxK -> Type.BoxK
                    Type.ValK -> Type.ValK
                    _ -> internalError "translateType: Not a valid tuple field type"
       return $ Type.typeApp (Type.UTupleT kinds) tys
     AppT op arg ->
       liftM2 Type.AppT (translateType' op) (translateType' arg)
     FunT dom rng ->
       liftM2 Type.FunT (translateType' dom) (translateType' rng)
     AllT (Domain param ty) rng -> do
       let v = toVar param
       dom <- translateType' ty
       rng' <- liftT (assume v dom) $ translateType' rng
       return $ Type.AllT (v ::: dom) rng'
     LamT doms body ->
       let mk_lambda (Domain param d : doms) body = do
             body' <- mk_lambda doms body
             d' <- translateType' d
             return $ Type.LamT (toVar param ::: d') body'
           mk_lambda [] body =
             translateType' body
       in mk_lambda doms body
     CoT kind dom rng -> do
       kind' <- translateType' kind
       dom' <- translateType' dom
       rng' <- translateType' rng
       return $ Type.typeApp (Type.CoT kind') [dom', rng']

translateGlobalFun pos f = do
  f' <- translateFun pos f
  return $ SystemF.FunEnt f'

translateFun pos f = do
  ty_binders <- mapM translateDomain $ fTyParams f
  liftT (assumeBinders ty_binders) $ do
    val_binders <- mapM translateDomain $ fParams f
    liftT (assumeBinders val_binders) $ do
      range <- translateType $ fRange f
      body <- translateExp $ fBody f
      return $ SystemF.FunM $
        SystemF.Fun { SystemF.funInfo = SystemF.mkExpInfo pos
                    , SystemF.funTyParams = map SystemF.TyPat ty_binders
                    , SystemF.funParams = map SystemF.patM val_binders
                    , SystemF.funReturn = range
                    , SystemF.funBody = body}

-- | Translate an AST expression to a System F expression.
--
--   Some translations require System F type information, which is looked up
--   as needed.
translateExp (L pos expression) =
  case expression
  of VarE v -> do
       tenv <- lift getTypeEnv
       case lookupDataConWithType (toVar v) tenv of
         Just (type_con, data_con) ->
           translateCon inf type_con data_con (toVar v) [] []
         Nothing ->
           return $ SystemF.ExpM $ SystemF.VarE inf (toVar v)
     IntE n ->
       return $ SystemF.ExpM $ SystemF.LitE inf (SystemF.IntL n int_type)
     FloatE n ->
       return $ SystemF.ExpM $ SystemF.LitE inf (SystemF.FloatL n float_type)
     TupleE es -> do
       es' <- mapM translateExp es
       types <- lift $ mapM SystemF.TypecheckMem.inferExpType es'
       let con = SystemF.TupleCon types
       return $ SystemF.ExpM $ SystemF.ConE inf con es'
     TAppE op arg ->
       let (op', args) = uncurryTypeApp op [arg]
       in translateApp inf op' args []
     AppE op arg ->
       let (op', ty_args, args) = uncurryApp op [arg]
       in translateApp inf op' ty_args args
     LamE f ->
       liftM (SystemF.ExpM . SystemF.LamE inf) $ translateFun pos f
     CaseE s alts -> do
       s' <- translateExp s
       alts' <- mapM (translateAlt . unLoc) alts
       return $ SystemF.ExpM $ SystemF.CaseE inf s' alts'
     LetE binder rhs body -> do
       rhs' <- translateExp rhs
       binder' <- translateDomain binder
       body' <- liftT (assumeBinder binder') $ translateExp body
       return $ SystemF.ExpM $ SystemF.LetE inf (SystemF.patM binder') rhs' body'
     LetTypeE dom rhs body -> do
       -- Define a type synonym.
       -- No code is actually generated from this expression.
       typ <- translateType rhs
       withLetTypeSynonym dom typ $ translateExp body
     LetfunE defs body -> assumeDefGroup defs $ do
       functions <- sequence [translateFun pos (dFun d) | L pos d <- defs]
       let systemf_defs = [applyDefAttributes False (dAttributes d) $
                           SystemF.mkDef (toVar $ dName d) f
                          | (L _ d, f) <- zip defs functions]
       let defgroup = SystemF.Rec systemf_defs
       body' <- translateExp body
       return $ SystemF.ExpM $ SystemF.LetfunE inf defgroup body'
     ExceptE t ->
       liftM (SystemF.ExpM . SystemF.ExceptE inf) $ translateType t
     CoerceE from_t to_t body -> do
       ft <- translateType from_t
       tt <- translateType to_t
       body' <- translateExp body
       return $ SystemF.ExpM $ SystemF.CoerceE inf ft tt body'
  where
    int_type = Type.VarT $ pyonBuiltin The_int
    float_type = Type.VarT $ pyonBuiltin The_float
    inf = SystemF.mkExpInfo pos

translateApp inf op ty_args args = do
  -- Is the operator a data constructor?
  tenv <- lift getTypeEnv
  case unLoc op of
    VarE v
      | Just (type_con, data_con) <- lookupDataConWithType (toVar v) tenv ->
          translateCon inf type_con data_con (toVar v) ty_args args
    _ -> do
      -- Create an application term
      op_exp <- translateExp op
      translateAppWithOperator inf op_exp ty_args args

translateAppWithOperator inf op_exp ty_args args = do
  arg_types <- mapM translateType ty_args
  arg_exps <- mapM translateExp args
  return $ SystemF.ExpM $ SystemF.AppE inf op_exp arg_types arg_exps

translateCon :: SystemF.ExpInfo -> DataType -> DataConType
             -> Var -> [RLType] -> [RLExp] -> TransM SystemF.ExpM
translateCon inf type_con data_con op ty_args args
  | length ty_args /= n_ty_args + n_ex_types =
    error $ show (getSourcePos inf) ++ ": Wrong number of type arguments to data constructor"
  | length args < n_args =
    -- Instead of producing an error, the constructor could be eta-expanded.
    error $ show (getSourcePos inf) ++ ": Too few arguments to data constructor"
  | otherwise = do
      -- Convert type arguments
      arg_types <- mapM translateType ty_args
      let con_ty_args = take n_ty_args arg_types
          con_ex_args = drop n_ty_args arg_types

      -- Convert constructor arguments
      let con_args = take n_args args
          other_args = drop n_args args
      con_args' <- mapM translateExp con_args
      let con = SystemF.VarCon op con_ty_args con_ex_args 
          con_exp = SystemF.ExpM $ SystemF.ConE inf con con_args'

      -- If any arguments remain, apply them
      if null other_args
        then return con_exp
        else translateAppWithOperator inf con_exp [] other_args
    
  where
    n_ty_args = length $ dataConPatternParams data_con
    n_ex_types = length $ dataConPatternExTypes data_con
    n_args = length $ dataConPatternArgs data_con

uncurryTypeApp e ty_args =
  case unLoc e
  of TAppE op arg -> uncurryTypeApp op (arg : ty_args)
     _ -> (e, ty_args)

uncurryApp e args =
  case unLoc e
  of AppE op arg -> uncurryApp op (arg : args)
     _ -> case uncurryTypeApp e []
          of (op, ty_args) -> (op, ty_args, args)

translateAlt (Alt (ConPattern con ty_args ex_types fields) body) = do
  ty_args' <- mapM translateType ty_args
  ty_binders <- mapM translateDomain ex_types
  let new_con = SystemF.VarDeCon (toVar con) ty_args' ty_binders
  liftT (assumeBinders ty_binders) $ do
    val_binders <- mapM translateDomain fields
    liftT (assumeBinders val_binders) $ do
      body' <- translateExp body
      return $ SystemF.AltM $
        SystemF.Alt { SystemF.altCon = new_con
                    , SystemF.altParams = map SystemF.patM val_binders
                    , SystemF.altBody = body'}

translateAlt (Alt (TuplePattern fields) body) = do
  val_binders <- mapM translateDomain fields
  let new_con = SystemF.TupleDeCon [t | _ ::: t <- val_binders]
  liftT (assumeBinders val_binders) $ do
    body' <- translateExp body
    return $ SystemF.AltM $
      SystemF.Alt { SystemF.altCon = new_con
                  , SystemF.altParams = map SystemF.patM val_binders
                  , SystemF.altBody = body'}

translateDecl (L pos (Decl name (FunEnt (L fun_pos f) attrs))) =
  let ResolvedVar v _ = name
  in liftM (applyDefAttributes True attrs . SystemF.mkDef v) $
     translateGlobalFun fun_pos f

translateDecl (L pos (Decl name (ConstEnt ty d attrs))) = do
  let ResolvedVar v _ = name
  core_ty <- translateType ty
  core_expr <- translateExp d
  let value = SystemF.Constant (SystemF.mkExpInfo pos) core_ty core_expr
      def = SystemF.mkDef v (SystemF.DataEnt value)
  return $ applyDefAttributes True attrs def

translateDecl _ =
  internalError "translateDecl"

translateDecls decls = mapM translateDecl decls

-------------------------------------------------------------------------------

createCoreFunctions var_supply tenv mod =
  case checkModule mod
  of Module decls -> do
       defs <- runTypeEvalM (runReaderT (translateDecls decls) Map.empty) var_supply tenv
       mapM_ check_def_type defs
       return $ SystemF.Module builtinModuleName [] [SystemF.Rec defs] []
  where
    -- Given a function definition, ensure that the function's actual type
    -- is consistent with the type found in the type environment.
    check_def_type def = do
      let fname = SystemF.definiendum def
          declared_type =
            case lookupType fname tenv
            of Just t -> t
               Nothing -> internalError $ "No type declared for function: " ++
                          show (SystemF.definiendum def)
          defined_type =
            SystemF.entityType $ SystemF.definiens def
      ok <- runTypeEvalM
            (Type.Compare.compareTypes declared_type defined_type)
            var_supply tenv
      when (not ok) $ fail ("Definition of function '" ++ show fname ++ "' doesn't match declared type")
           
