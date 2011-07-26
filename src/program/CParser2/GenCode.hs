
module CParser2.GenCode (createCoreFunctions) where

import Control.Monad

import Common.SourcePos
import Common.Error
import Common.Label
import Builtins.Builtins
import CParser2.AST
import qualified SystemF.Syntax as SystemF
import qualified SystemF.MemoryIR as SystemF
import Type.Environment
import qualified Type.Eval
import Type.Var
import Type.Type(Binder(..), Level(..))
import qualified Type.Type as Type

-- | Extract function declarations from a module
checkModule :: Module Resolved -> Module Resolved
checkModule mod@(Module decls) 
  | any (not . is_fun_decl) decls =
      internalError "Expecting function declarations only"
  | otherwise = mod
  where
    is_fun_decl ldecl =
      case unLoc ldecl
      of Decl _ (FunEnt _ _) -> True
         _                   -> False

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

    -- There should be at most one inlining-related attribute
    check_inlining_attrs =
      case filter (`elem` [InlineSequentialAttr, InlineFinalAttr]) attrs
      of []  -> ()
         [_] -> ()
         _   -> internalError "Functions may not have more than one inlining attribute"

    insert_attribute InlineSequentialAttr ann =
      ann {SystemF.defAnnInlining = SystemF.InlSequential}
    
    insert_attribute InlineFinalAttr ann =
      ann {SystemF.defAnnInlining = SystemF.InlFinal}

    insert_attribute _ _ =
      internalError "Unexpected function attribute"

applyDefAttributes :: [Attribute] -> (SystemF.Def SystemF.Mem -> SystemF.Def SystemF.Mem)
applyDefAttributes attrs = SystemF.modifyDefAnnotation (defAttributes attrs)

-- | Determine the type of an expression.
expType :: RLExp -> TypeEvalM Type.Type
expType (L pos expression) =
  case expression
  of VarE v -> do
       Just ty <- askTypeEnv (lookupType (toVar v))
       return ty
     IntE _ -> return $ Type.VarT $ pyonBuiltin the_int
     TAppE op arg -> do
       -- Compute the result of type application
       op_type <- expType op
       arg' <- translateType arg
       tenv <- getTypeEnv
       let arg_kind = Type.Eval.typeKind tenv arg'
       Just rt <- Type.Eval.typeOfTypeApp op_type arg_kind arg'
       return rt
     AppE op arg -> do
       -- Compute the applied type
       op_type <- expType op
       arg_type <- expType arg
       Just rt <- Type.Eval.typeOfApp op_type arg_type
       return rt
     LamE f -> translateType $ funType pos f
     CaseE _ (L _ alt:_) -> do
       ty_binders <- mapM translateDomain $ altExTypes (altPattern alt)
       assumeBinders ty_binders $ do
         val_binders <- mapM translateDomain $ altFields (altPattern alt)
         assumeBinders val_binders $ do
           expType (altBody alt)
     LetE dom _ body -> do
       binder <- translateDomain dom
       assumeBinder binder $ expType body
     LetfunE defs body -> do
       assumeDefGroup defs $ expType body
     ExceptE t -> translateType t

expKind :: RLExp -> TypeEvalM Type.Kind
expKind e = do
  t <- expType e
  tenv <- getTypeEnv
  return $ Type.Eval.typeKind tenv t

typeKind :: RType -> TypeEvalM Type.Kind
typeKind t =
  case t
  of VarT v -> do
       Just k <- askTypeEnv (lookupType (toVar v))
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
       assume (toVar v) dom' $ typeKind $ unLoc rng

assumeDefGroup :: [LDef Resolved] -> TypeEvalM b -> TypeEvalM b
assumeDefGroup defs m = do
  -- Add function types to environment
  let vars = [toVar $ dName d | L _ d <- defs]
  fun_types <- sequence [translateType $ funType pos (dFun d)
                        | L pos d <- defs]
  assumeBinders (zipWith (:::) vars fun_types) $ m

-------------------------------------------------------------------------------

toVar (ResolvedVar v _) = v

translateDomain :: Domain Resolved -> TypeEvalM Type.Binder
translateDomain (Domain param ty) =
  liftM (toVar param :::) $ translateType ty

-- | Translate an AST type to a 'mem' type.
--   First the type is translated to a 'spec' type, then 
--   it's converted to 'mem'.
translateType :: RLType -> TypeEvalM Type.Type
translateType t = liftM specToMemType $ translateType' t

-- | Translate an AST type to a specification type.  This function is
--   only used by 'translateType'.
translateType' :: RLType -> TypeEvalM Type.Type
translateType' lty =
  case unLoc lty
  of VarT v -> return $ Type.VarT (toVar v)
     IntIndexT n -> return $ Type.IntT n
     TupleT tuple_args -> do
       -- Get kinds of type arguments
       tenv <- getTypeEnv
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
       rng' <- assume v dom $ translateType' rng
       return $ Type.AllT (v ::: dom) rng'

translateFun pos f = do
  ty_binders <- mapM translateDomain $ fTyParams f
  assumeBinders ty_binders $ do
    val_binders <- mapM translateDomain $ fParams f
    assumeBinders val_binders $ do
      range <- translateType $ fRange f
      body <- translateExp $ fBody f
      return $ SystemF.FunM $
        SystemF.Fun { SystemF.funInfo = SystemF.mkExpInfo pos
                    , SystemF.funTyParams = map SystemF.TyPatM ty_binders
                    , SystemF.funParams = map SystemF.patM val_binders
                    , SystemF.funReturn = SystemF.TypM range
                    , SystemF.funBody = body}

-- | Translate an AST expression to a System F expression.
--
--   Some translations require System F type information, which is looked up
--   as needed.
translateExp (L pos expression) =
  case expression
  of VarE v ->
       return $ SystemF.ExpM $ SystemF.VarE inf (toVar v)
     IntE n ->
       return $ SystemF.ExpM $ SystemF.LitE inf (SystemF.IntL n int_type)
     TupleE es ->
       liftM (SystemF.ExpM . SystemF.UTupleE inf) $ mapM translateExp es
     TAppE op arg -> do
       let (op', args) = uncurryTypeApp op [arg]
       op_exp <- translateExp op'
       arg_types <- mapM (liftM SystemF.TypM . translateType) args
       return $ SystemF.ExpM $ SystemF.AppE inf op_exp arg_types []
     AppE op arg -> do
       let (op', ty_args, args) = uncurryApp op [arg]
       op_exp <- translateExp op'
       arg_types <- mapM (liftM SystemF.TypM . translateType) ty_args
       arg_exps <- mapM translateExp args
       return $ SystemF.ExpM $ SystemF.AppE inf op_exp arg_types arg_exps
     LamE f ->
       liftM (SystemF.ExpM . SystemF.LamE inf) $ translateFun pos f
     CaseE s alts -> do
       s' <- translateExp s
       alts' <- mapM (translateAlt . unLoc) alts
       return $ SystemF.ExpM $ SystemF.CaseE inf s' alts'
     LetE binder rhs body -> do
       rhs' <- translateExp rhs
       binder' <- translateDomain binder
       body' <- assumeBinder binder' $ translateExp body
       return $ SystemF.ExpM $ SystemF.LetE inf (SystemF.patM binder') rhs' body'
     LetfunE defs body -> assumeDefGroup defs $ do
       functions <- sequence [translateFun pos (dFun d) | L pos d <- defs]
       let systemf_defs = [applyDefAttributes (dAttributes d) $
                           SystemF.mkDef (toVar $ dName d) f
                          | (L _ d, f) <- zip defs functions]
       let defgroup = SystemF.Rec systemf_defs
       body' <- translateExp body
       return $ SystemF.ExpM $ SystemF.LetfunE inf defgroup body'
     ExceptE t ->
       liftM (SystemF.ExpM . SystemF.ExceptE inf) $ translateType t
  where
    int_type = Type.VarT $ pyonBuiltin the_int
    inf = SystemF.mkExpInfo pos

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
  ty_args' <- mapM (liftM SystemF.TypM . translateType) ty_args
  ty_binders <- mapM translateDomain ex_types
  assumeBinders ty_binders $ do
    val_binders <- mapM translateDomain fields
    assumeBinders val_binders $ do
      body' <- translateExp body
      return $ SystemF.AltM $
        SystemF.DeCon { SystemF.altConstructor = toVar con
                      , SystemF.altTyArgs = ty_args'
                      , SystemF.altExTypes = map SystemF.TyPatM ty_binders
                      , SystemF.altParams = map SystemF.patM val_binders
                      , SystemF.altBody = body'}

translateAlt (Alt (TuplePattern fields) body) = do
  val_binders <- mapM translateDomain fields
  assumeBinders val_binders $ do
    body' <- translateExp body
    return $ SystemF.AltM $
      SystemF.DeTuple { SystemF.altParams = map SystemF.patM val_binders
                      , SystemF.altBody = body'}

translateDecl (L pos (Decl name (FunEnt (L fun_pos f) attrs))) =
  let ResolvedVar v _ = name
  in liftM (applyDefAttributes attrs . SystemF.mkDef v) $ translateFun fun_pos f

translateDecl _ =
  internalError "translateDecl"

-------------------------------------------------------------------------------

createCoreFunctions var_supply tenv mod =
  case checkModule mod
  of Module decls -> do
       defs <- runTypeEvalM (mapM translateDecl decls) var_supply tenv
       return $ SystemF.Module builtinModuleName [] [SystemF.Rec defs] []
      