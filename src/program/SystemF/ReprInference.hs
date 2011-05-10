{-| Infer data structure representations.

This module replaces the old "SystemF.Representation" module.

-}

{-# LANGUAGE FlexibleInstances #-}
module SystemF.ReprInference(representationInference)
where

import Control.Monad.Reader
import Debug.Trace

import Text.PrettyPrint.HughesPJ

import Common.MonadLogic
import Common.Identifier
import Common.Supply
import Common.Error
import Builtins.Builtins
import Type.Environment
import Type.Type
import SystemF.Syntax
import SystemF.Print
import SystemF.TypecheckSF

import Globals
import GlobalVar

type Kind = Type

-- | The representation inference monad.
--
--   Specification types are tracked for variables that are in scope.
--   New variables can be created.
newtype RI a = RI {unRI :: ReaderT (IdentSupply Var, TypeEnv) IO a}

instance Functor RI where
  fmap f (RI m) = RI (fmap f m)

instance Monad RI where
  return x = RI (return x)
  m >>= k = RI (unRI m >>= unRI . k)

instance Supplies RI (Ident Var) where
  fresh = RI (ReaderT (\(supply, _) -> supplyValue supply))

assume :: Var -> Type -> RI a -> RI a
assume v t m = RI (local add_type $ unRI m)
  where
    add_type (supply, env) = (supply, insertType v (ValRT ::: t) env)

riLookupType :: Var -> RI Type
riLookupType v = RI $ asks lookup_type
  where
    lookup_type (_, env) =
      case lookupType v env
      of Just (ValRT ::: rt) -> rt
         _ -> internalError $ "riLookupType: not found: " ++ show v

-------------------------------------------------------------------------------

data TypeMode =
    NaturalMode                   -- ^ Natural representation
  | BoxedMode                     -- ^ Canonical boxed representation

-- | Convert a System F kind to a representation-specific kind.
cvtKind :: Kind -> Kind
cvtKind k =
  case k
  of VarT v
       | v == pureV     -> bareT
       | v == intindexV -> intindexT
     ValPT Nothing ::: k1 `FunT` ValRT ::: k2 ->
       ValPT Nothing ::: cvtKind k1 `FunT` ValRT ::: cvtKind k2
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
           of Just (op, [arg]) | op `isPyonBuiltin` the_Boxed ->
                case fromVarApp arg
                of Just (op, [arg2]) | op `isPyonBuiltin` the_Stored -> return arg2
                   _ -> internalError "coerceType"
              _ -> internalError "coerceType"
       | e_kv == boxV && g_kv == valV ->
           return $
           varApp (pyonBuiltin the_Boxed)
           [varApp (pyonBuiltin the_Stored) [g_t]]
       | e_kv == boxV && g_kv == bareV ->
           return $ boxedType g_t
       | e_kv == bareV && g_kv == valV ->
           return $varApp (pyonBuiltin the_Stored) [g_t]
       | e_kv == bareV && g_kv == boxV ->
           return $ bareType g_t
     (ValPT Nothing ::: e_dom `FunT` ValRT ::: e_rng,
      ValPT Nothing ::: g_dom `FunT` ValRT ::: g_rng)
       | same_kind e_dom g_dom && same_kind e_rng g_rng ->
           return g_t -- No need to coerce
       | otherwise -> do
           param <- newAnonymousVar TypeLevel
           coerced_param <- coerceType e_dom g_dom (VarT param)
           coerced_result <- coerceType g_rng e_rng $ AppT g_t coerced_param
           return $ LamT param e_dom (ValRT ::: coerced_result)
  where
    same_kind (VarT k1) (VarT k2) = k1 == k2
    same_kind (ValPT Nothing ::: k1 `FunT` ValRT ::: k2)
              (ValPT Nothing ::: k3 `FunT` ValRT ::: k4) =
      same_kind k1 k3 && same_kind k2 k4
    same_kind _ _ = False

-- | Type coercions
--
-- * writeType : bare -> write
-- * boxedType : bare -> box
-- * bareType  : box  -> bare
writeType, boxedType, bareType :: Type -> Type
writeType t = varApp (pyonBuiltin the_write) [t]
boxedType t = varApp (pyonBuiltin the_BoxedType) [t]
bareType t  = varApp (pyonBuiltin the_BareType) [t]

-- | Convert a System F type to its natural representation
cvtNaturalType :: Type -> RI (Type, Kind)
cvtNaturalType = cvtType NaturalMode

-- | Convert a System F type to boxed representation
cvtBoxedType :: Type -> RI Type
cvtBoxedType t = fmap fst $ cvtType BoxedMode t

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

-- | Helper function for 'cvtType'.  If mode is 'BoxedMode', coerce to
--   a boxed kind.
wrapForMode :: TypeMode -> Type -> Kind -> RI (Type, Kind)
wrapForMode NaturalMode t k = return (t, k)
wrapForMode BoxedMode   t k = do
  t' <- coerceType k boxT t
  return (t', boxT)

-- | Convert a System F type to a representation type.
--
--   If converting in 'BoxedMode', the return type always has @box@ kind.
--   In 'NaturalMode', the return type has the preferred kind for its
--   representation.
cvtType :: TypeMode -> Type -> RI (Type, Kind)
cvtType mode (VarT v) = do
  k <- riLookupType v
  wrapForMode mode (VarT v) k

cvtType mode (AppT t1 t2) = do
  (t1', t1_k) <- cvtNaturalType t1
  case t1_k of
    ValPT Nothing ::: dom_k `FunT` ValRT ::: rng_k -> do
      -- Convert and coerce argument type
      (t2', t2_k) <- cvtNaturalType t2
      t2'' <- coerceType t2_k dom_k t2'
      wrapForMode mode (AppT t1' t2'') rng_k
    _ -> internalError "cvtNaturalType: Invalid type"

cvtType mode (ValPT Nothing ::: t1 `FunT` ValRT ::: t2) = do
  -- Function type
  dom <- case mode 
         of NaturalMode -> fmap fst $ cvtParamType t1
            BoxedMode   -> cvtBoxedType t1
  rng <- case mode
         of NaturalMode -> fmap fst $ cvtReturnType t2
            BoxedMode   -> cvtBoxedType t2
  return (ValPT Nothing ::: dom `FunT` ValRT ::: rng, boxT)

cvtType mode (AllT a t1 (ValRT ::: t2)) = do
  -- Forall type
  let dom = cvtKind t1
  rng <- assume a dom $ fmap fst $ cvtType mode t2 
  return (AllT a dom (ValRT ::: rng), boxT)

-- | Print debugging information while converting a type
dbCvtNaturalType :: Type -> RI (Type, Kind)
dbCvtNaturalType t = do
  (t', k) <- cvtNaturalType t
  RI $ lift $ print $ text "Convert NT" <+> (pprType t $$ pprType t')
  return (t', k)

dbCvtLocalType :: Type -> RI (Type, Kind)
dbCvtLocalType t = do
  (t', k) <- cvtLocalType t
  RI $ lift $ print $ text "Convert LT" <+> (pprType t $$ pprType t')
  return (t', k)

dbCvtParamType :: Type -> RI (Type, Kind)
dbCvtParamType t = do
  (t', k) <- cvtParamType t
  RI $ lift $ print $ text "Convert PT" <+> (pprType t $$ pprType t')
  return (t', k)

dbCvtReturnType :: Type -> RI (Type, Kind)
dbCvtReturnType t = do
  (t', k) <- cvtReturnType t
  RI $ lift $ print $ text "Convert RT" <+> (pprType t $$ pprType t')
  return (t', k)

-------------------------------------------------------------------------------
-- Coercing expressions

data Coercion

coerceExp :: Type               -- ^ Given type
          -> Type               -- ^ Expected type
          -> RI Coercion        -- ^ Computes the coercion
coerceExp g_type e_type = do
  RI $ lift $ print $ text "Coerce " <+> (pprType g_type $$ text "to" <+> pprType e_type)
  return (internalError "coerceExp: Not implemented")

-------------------------------------------------------------------------------

reprTyPat :: TyPat SF -> (TyPat SF -> RI a) -> RI a
reprTyPat (TyPatSF v kind) k =
  let kind' = cvtKind kind
  in assume v kind' $ k (TyPatSF v kind')

reprLocalPat :: PatSF -> (PatSF -> RI a) -> RI a
reprLocalPat (VarP v t) k = do
  (t', _) <- dbCvtLocalType t
  assume v t' $ k (VarP v t')

reprParam :: PatSF -> (PatSF -> RI a) -> RI a
reprParam (VarP v t) k = do
  (t', _) <- dbCvtParamType t
  assume v t' $ k (VarP v t')

reprRet :: RetSF -> RI RetSF
reprRet (RetSF t) = fmap (RetSF . fst) $ dbCvtReturnType t

-- | Convert an expression's representation
reprExp :: ExpSF -> RI (ExpSF, Type)
reprExp expression =
  case fromExpSF expression
  of VarE _ v -> do
       v_type <- riLookupType v
       return (expression, v_type)
     LitE _ l -> return (expression, literalType l)
     AppE inf op ty_args args ->
       reprApp inf op ty_args args
     LamE inf f -> do
       f' <- reprFun f
       let ret_type = case funReturn $ fromFunSF f of RetSF t -> t
       return (ExpSF $ LamE inf f', ret_type)
     LetE inf pat rhs body -> do
       (rhs', rhs_type) <- reprExp rhs
       reprLocalPat pat $ \pat' -> do
         let pat_type = case pat' of VarP _ t -> t
         rhs_coercion <- coerceExp rhs_type pat_type

         -- TODO: coerce RHS
         (body', body_type) <- reprExp body
         return (ExpSF $ LetE inf pat' rhs' body', body_type)
     LetfunE inf defs body ->
       withDefs defs $ \defs' -> do
         (body', body_type) <- reprExp body
         return (ExpSF $ LetfunE inf defs' body', body_type)
     CaseE inf scr alts -> do 
       (scr', scr_type) <- reprExp scr
       -- TODO: coerce scrutinee
       (alts', alt_types) <- mapAndUnzipM reprAlt alts
       return (ExpSF $ CaseE inf scr' alts', head alt_types)
     ExceptE inf (ValRT ::: t) -> do
       (t', _) <- dbCvtNaturalType t
       return (ExpSF $ ExceptE inf (ValRT ::: t'), t')

reprApp inf op ty_args args = do
  (op', op_type) <- reprExp op
  (ty_args', _) <- mapAndUnzipM (dbCvtNaturalType . fromTypSF) ty_args
  -- TODO: coerce type arguments
  let inst_op_type = drop_ty_args op_type ty_args'

  (args', arg_types) <- mapAndUnzipM reprExp args
  (coercions, return_type) <- coerce_arguments inst_op_type arg_types
  -- TODO: coerce arguments
  return (ExpSF $ AppE inf op ty_args args, return_type)
  where
    -- TODO: This should actually construct a substitution, not just drop
    -- arguments
    drop_ty_args (AllT _ _ (ValRT ::: op_type)) (arg:args) =
      drop_ty_args op_type args

    drop_ty_args op_type [] =
      op_type

    drop_ty_args op_type _ =
      internalError $ "reprApp: " ++ show (pprType op_type) ++ "\n" ++ show (pprExp op)

    coerce_arguments (FunT (ValPT Nothing ::: param_type) (ValRT ::: ret_type))
                     (arg_type : arg_types) = do
      arg_coercion <- coerceExp arg_type param_type
      (arg_coercions, rt) <- coerce_arguments ret_type arg_types 
      return (arg_coercion : arg_coercions, rt)
    
    coerce_arguments op_type [] = return ([], op_type)

-- | Convert a case alternative's representation.
--
--   To ensure that all alternatives in a multi-branch case have the same
--   representation, the body's representation is chosen based only on its
--   type.
reprAlt :: AltSF -> RI (AltSF, Type)
reprAlt (AltSF alt) = do
  (ty_args, _) <- mapAndUnzipM (dbCvtNaturalType . fromTypSF) (altTyArgs alt)
  withMany reprTyPat (altExTypes alt) $ \ex_types ->
    withMany reprParam (altParams alt) $ \params -> do
      (body, body_type) <- reprExp (altBody alt)
      -- TODO: coerce body to natural representation
      
      let new_alt = AltSF $ Alt { altConstructor = altConstructor alt
                                , altTyArgs = map TypSF ty_args
                                , altExTypes = ex_types
                                , altParams = params
                                , altBody = body} 
      return (new_alt, body_type)

reprFun :: FunSF -> RI FunSF
reprFun (FunSF f) =
  withMany reprTyPat (funTyParams f) $ \ty_params ->
  withMany reprParam (funParams f) $ \params -> do
    (body, body_type) <- reprExp (funBody f)
    ret <- reprRet (funReturn f)
    
    -- TODO: coerce body to match the return type
    rhs_coercion <- coerceExp body_type (retSFType ret)
    return $ FunSF (Fun { funInfo = funInfo f
                        , funTyParams = ty_params
                        , funParams = params
                        , funReturn = ret
                        , funBody = body})

withDefs :: DefGroup (Def SF) -> (DefGroup (Def SF) -> RI a) -> RI a
withDefs (NonRec def) k = do
  def' <- traceShow (pprDef def) $ mapMDefiniens reprFun def
  assume (definiendum def') (functionTypeNew $ definiens def') $ k (NonRec def')

withDefs (Rec defs) k = do
  (types, _) <- mapAndUnzipM (dbCvtNaturalType . functionTypeNew . definiens) defs 
  assume_functions (zip (map definiendum defs) types) $ do
    defs' <- mapM (mapMDefiniens reprFun) defs
    k (Rec defs')
  where
    assume_functions ((v, t) : fs) m = assume v t $ assume_functions fs m
    assume_functions [] m = m

reprExport e = do
  f <- reprFun $ exportFunction e
  return $ Export { exportSourcePos = exportSourcePos e 
                  , exportSpec = exportSpec e
                  , exportFunction = f}

reprTopLevelDefs :: [DefGroup (Def SF)]
                 -> [Export SF]
                 -> RI ([DefGroup (Def SF)], [Export SF])
reprTopLevelDefs defgroups exports = go id defgroups
  where
    go hd (g:gs) = withDefs g $ \g' -> go (hd . (g':)) gs
    go hd [] = do es <- mapM reprExport exports
                  return (hd [], es)

reprModule :: Module SF -> RI (Module SF)
reprModule (Module mod_name defs exports) = do
  (defs', exports') <- reprTopLevelDefs defs exports
  return (Module mod_name defs' exports')

-- | Perform representation inference.
--
--   The specification type environment is used for representation inference.
representationInference :: Module SF
                        -> IO (Module SF)
representationInference mod = do
  withTheNewVarIdentSupply $ \supply -> do
    type_env <- readInitGlobalVarIO the_specTypes
    let context = (supply, type_env)
    runReaderT (unRI $ reprModule mod) context
