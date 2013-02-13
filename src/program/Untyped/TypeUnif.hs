{-| Unification, substitution, and comparison on types.
-}

{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
module Untyped.TypeUnif
       (-- * Manipulating 'HMType's
        instantiateTyVar,
        appTy, appTys, appTyCon, functionTy, tupleTy,
        deconstructFunctionType,
        uncurryApp,
        isTFAppOfVar,
        headIsInjective,
        isGround,
        predicatesEqual,
        predicateFreeVars,
        tySchemeFreeVars,

        -- * Substitutions
        CSubstitution,
        emptyCSubstitution,
        singletonCSubstitution,
        listCSubstitution,
        lookupCSubstitution,
        lookupCSubstitution',
        semiUnifyC,
        matchC,
        substituteType,
        CTerm(..),
        
        -- * Pretty-printing
        Ppr, runPpr, pprUVar,
        pprTyCon,
        pprType,
        pprPredicate,
        pprConstraint,
        pprQualified,
        pprTyScheme,
        pprTypeBinding,
        pprTypeEnvironment,
        pprValueBinding,
        pprValueEnvironment
       )
where

import Prelude hiding(mapM)
  
import Control.Applicative hiding(empty)
import Control.Monad hiding(mapM, forM)
import Control.Monad.Trans
import Data.Function
import Data.IORef
import Data.List
import Data.Traversable
import Data.Typeable(Typeable)
import qualified Data.Map as Map
import Data.Monoid hiding((<>))
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ
import System.IO.Unsafe

import Common.Error
import Common.Identifier
import Common.Label
import Common.MonadLogic
import Common.Supply
import qualified SystemF.Syntax as SF
import qualified Type.Type as SF
import {-# SOURCE #-} Untyped.Classes
import qualified Untyped.Syntax as Untyped
import Untyped.Unif
import Untyped.Type
import {-# SOURCE #-} Untyped.TIMonad
import Untyped.Kind
import Untyped.Variable

-- | Report a kind error.  Give very rough information about where the
--   error occurred.
kindError loc =
  error $ "Kind error in " ++ loc

instance UTerm HMType where
  type NormalizeMonadConstraint HMType m = EnvMonad m
  type UConstraint HMType = Constraint

  kind = typeKind
  
  normalize t =
    case t
    of VarTy v -> normalizeUVar v
       TFunAppTy f ts -> do
         -- Reduce type functions
         Just family <- getTyConTypeFunction f
         reduced <- reduceTypeFunction family ts
         case reduced of
           Just t' -> normalize t'
           Nothing -> return t

       -- Other terms are not reducible
       _ -> return t

  injectU v = VarTy v

  projectU (VarTy v) = Just v
  projectU _         = Nothing
  
  listU t =
    case t
    of AppTy t1 t2 -> ([t1, t2], \ [t1', t2'] -> AppTy t1' t2')
       TFunAppTy tc ts -> (ts, \ts' -> check_length ts ts' $ TFunAppTy tc ts')
       VarTy _ -> no_subterms
       ConTy _ -> no_subterms
       FunTy _ -> no_subterms
       TupleTy _ -> no_subterms
       AnyTy _ -> no_subterms
    where
      no_subterms = ([], \ [] -> t)
      check_length ts ts' x
        | length ts == length ts' = x
        | otherwise = internalError "listU: Wrong number of type parameters"

  zipU t1 t2 =
    case (t1, t2)
    of (VarTy v1,   VarTy v2)   | v1 == v2 -> no_subterms
       (ConTy c1,   ConTy c2)   | c1 == c2 -> no_subterms
       (FunTy n1,   FunTy n2)   | n1 == n2 -> no_subterms
       (TupleTy n1, TupleTy n2) | n1 == n2 -> no_subterms
       (AnyTy k1,   AnyTy k2)   | k1 == k2 -> no_subterms
       (AppTy s t,  AppTy u v)             -> app (s, t) (u, v)
       (TFunAppTy c1 xs, TFunAppTy c2 ys)
                                | c1 == c2 -> tfun (c1, xs) (c2, ys)
       _ -> Nothing
    where
      no_subterms = Just ([], [], \ [] -> t1)
      app (s, t) (u, v) =  Just ([],
                                 [(s, u), (t, v)],
                                 \ [s', t'] -> AppTy s' t')
      tfun (c1, xs) (c2, ys) = Just ([],
                                     zip xs ys,
                                     \ xs' -> check_length xs xs' $
                                              TFunAppTy c1 xs')
      check_length ts ts' x
        | length ts == length ts' = x
        | otherwise = internalError "zipU: Wrong number of type parameters"

  deferableU (TFunAppTy _ _) = True
  deferableU _               = False

  deferUnification t1 t2 = [t1 `IsEqual` t2]

deconstructFunctionType :: NormalizeContext HMType m =>
                          HMType -> m ([HMType], HMType)
deconstructFunctionType ty = do
  (op, args) <- uncurryApp ty
  case op of
    FunTy n | 1 + n == length args -> return (init args, last args)
    _ -> internalError "deconstructFunctionType: Not a function type"

uncurryApp :: NormalizeContext HMType m => HMType -> m (HMType, [HMType])
uncurryApp ty = unc ty []
  where
    unc ty args = do
      ty' <- normalize ty
      case ty' of
        AppTy op arg -> unc op (arg : args)
        TFunAppTy op args' -> return (ConTy op, args' ++ args)
        _ -> return (ty', args)

-- | Return 'True' if the expression is a type function application
--   containing a unifiable variable somewhere among its arguments.
isTFAppOfVar :: NormalizeContext HMType m => HMType -> m Bool
isTFAppOfVar ty = do
  (head, args) <- uncurryApp ty
  case head of
    ConTy c | isTyFun c -> anyM hasFreeUVar args
    _ -> return False

-- | Return 'True' if the expression's head is an injective type
--   constructor.  Return 'False' if it is a variable or function.
headIsInjective :: NormalizeContext HMType m => HMType -> m Bool
headIsInjective ty = do
  (head, _) <- uncurryApp ty
  return $! isInjConstructor head

-- | Return 'True' if there are no type variables in the term.
isGround :: NormalizeContext HMType m => HMType -> m Bool
isGround ty = normalize ty >>= examine
  where
    examine (VarTy _)             = return False
    examine (ConTy c) | isTyVar c = return False
    examine (ConTy _)             = return True
    examine (AppTy t1 t2)         = isGround t1 >&&> isGround t2
    examine (FunTy _)             = return True
    examine (TupleTy _)           = return True
    examine (TFunAppTy _ ts)      = allM isGround ts
    examine (AnyTy _)             = return True
    
-- | Decide whether two predicates are equal.
--   The predicates must match exactly; isomorphic predicates are considered
--   unequal.
predicatesEqual :: NormalizeContext HMType m =>
                   Predicate -> Predicate -> m Bool
predicatesEqual (IsInst cls1 t1) (IsInst cls2 t2)
  | cls1 == cls2 = uEqual t1 t2
  | otherwise    = return False

predicatesEqual (IsEqual t1 t2) (IsEqual s1 s2) =
  uEqual t1 s1 >&&> uEqual t2 s2

predicatesEqual _ _ = return False

predicateFreeVars :: NormalizeContext HMType m => Predicate -> m TyVarSet 
predicateFreeVars (IsInst _ ty) = freeUVars ty
predicateFreeVars (IsEqual t1 t2) =
  liftM2 Set.union (freeUVars t1) (freeUVars t2)

tySchemeFreeVars :: NormalizeContext HMType m => TyScheme -> m TyVarSet
tySchemeFreeVars (Qualified _ cst e) = do
  fv1 <- Set.unions `liftM` mapM predicateFreeVars cst
  fv2 <- freeUVars e
  return $ fv1 `Set.union` fv2

-------------------------------------------------------------------------------
-- Substitutions

-- | A substitution of terms for fixed type variables
newtype CSubstitution = CSubstitution (Map.Map TyCon HMType)

emptyCSubstitution :: CSubstitution
emptyCSubstitution = CSubstitution Map.empty

singletonCSubstitution :: TyCon -> HMType -> CSubstitution
singletonCSubstitution v t = CSubstitution $ Map.singleton v t

listCSubstitution :: [(TyCon, HMType)] -> CSubstitution
listCSubstitution xs = CSubstitution $ Map.fromList xs

insertCSubstitution :: TyCon -> HMType -> CSubstitution -> CSubstitution
insertCSubstitution v t (CSubstitution m) 
  | not $ isTyVar v = internalError "insertCSubstitution: Not a variable"
  | otherwise = CSubstitution (Map.insert v t m)

deleteCSubstitution :: TyCon -> CSubstitution -> CSubstitution
deleteCSubstitution v (CSubstitution m) = CSubstitution $ Map.delete v m

keysCSubstitution :: CSubstitution -> TyConSet
keysCSubstitution (CSubstitution m) = Map.keysSet m

lookupCSubstitution :: TyCon -> CSubstitution -> Maybe HMType
lookupCSubstitution v (CSubstitution m) = Map.lookup v m

lookupCSubstitution' :: TyCon -> CSubstitution -> HMType
lookupCSubstitution' v m = case lookupCSubstitution v m of Just t -> t

-- | Find a substitution and constraint that unifies the first term with the
--   second.  Only the indicated variables may be unified.
semiUnifyC :: NormalizeContext HMType m =>
              TyConSet          -- ^ Unifiable variables
           -> CSubstitution     -- ^ Current substitution
           -> HMType            -- ^ Unifiable term
           -> HMType            -- ^ Rigid term
           -> m (Maybe (CSubstitution, Constraint))
semiUnifyC unifiable_set subst t1 t2 = do
  t1_c <- normalize t1
  t2_c <- normalize t2
  case () of
    () | ConTy v <- t1_c, isTyVar v, v `Set.member` unifiable_set,
         Just t1' <- lookupCSubstitution v subst ->
           -- This term must match without further substitution
           require =<< uEqual t1' t2_c
       | ConTy v <- t1_c, isTyVar v ->
           -- This variable can be unified.  Unify it with t2_c
           let subst' = insertCSubstitution v t2_c subst
           in return $ Just (subst', mempty)

       -- Defer unification of the first term if possible
       | deferableU t1_c ->
           return $ Just (subst, deferUnification t1_c t2_c)

       -- Other terms must match
       | Just (cst, subterms, _) <- zipU t1_c t2_c ->
           unify_list cst subst subterms

       -- Semi-unification failed
       | otherwise -> return Nothing
  where
    require True  = return $ Just (subst, mempty)
    require False = return Nothing

    unify_list cst subst subterms = go [cst] subst subterms
      where
        go rcsts subst ((t1, t2) : pairs) =
          semiUnifyC unifiable_set subst t1 t2 >>= next
          where
            next (Just (subst', cst)) = go (cst:rcsts) subst' pairs
            next Nothing              = return Nothing
        go rcsts subst [] = return $ Just (subst, mconcat $ reverse rcsts)

matchC :: NormalizeContext HMType m =>
         TyConSet -> HMType -> HMType -> m (Maybe (CSubstitution, Constraint))
matchC unifiable_set = semiUnifyC unifiable_set emptyCSubstitution

-- | Terms containing non-unifiable type variables
class CTerm a where
  freeC :: NormalizeContext HMType m => a -> m TyConSet
  substituteC :: NormalizeContext HMType m => CSubstitution -> a -> m a

instance CTerm () where
  freeC () = return Set.empty
  substituteC _ () = return ()

instance CTerm a => CTerm [a] where
  freeC xs = Set.unions `liftM` mapM freeC xs
  substituteC subst xs = mapM (substituteC subst) xs

instance (CTerm a, CTerm b) => CTerm (a, b) where
  freeC (x, y) = liftM2 Set.union (freeC x) (freeC y)
  substituteC subst (x, y) =
    liftM2 (,) (substituteC subst x) (substituteC subst y)

instance CTerm (FOConstructor a) where
  freeC _         = return Set.empty
  substituteC _ x = return x

instance CTerm HMType where
  freeC t = go =<< normalize t
    where
      go (ConTy v)
        | isTyVar v =
            return $ Set.singleton v
      go t =
        let (subterms, _) = listU t
        in Set.unions `liftM` mapM freeC subterms

  substituteC subst t = go =<< normalize t
    where
      go (ConTy v)
        | isTyVar v, Just t' <- lookupCSubstitution v subst =
            return t'
      go t =
        let (subterms, rebuild) = listU t
        in rebuild `liftM` mapM (substituteC subst) subterms

instance CTerm a => CTerm (Instance a) where
  freeC (Instance head body) = liftM2 Set.union (freeC head) (freeC body)
  substituteC subst (Instance head body) =
    liftM2 Instance (substituteC subst head) (substituteC subst body)

instance CTerm a => CTerm (Qualified a) where
  freeC (Qualified params cst x) = do
    fv1 <- freeC x
    fv2 <- freeC cst
    return $ foldr Set.delete (Set.union fv1 fv2) params

  substituteC subst (Qualified params cst x) = do
    -- Instead of throwing an error, should we remove 'params'
    -- from the substituted set?
    let keys = keysCSubstitution subst
    when (any (`Set.member` keys) params) $
      internalError "substituteC: Unexpected shadowing"

    cst' <- substituteC subst cst
    x' <- substituteC subst x
    return $ Qualified params cst' x'

instance CTerm Predicate where
  freeC (IsInst cls ty) = freeC ty
  freeC (IsEqual s t) = liftM2 Set.union (freeC s) (freeC t)

  substituteC subst (IsInst cls ty) = do
    ty' <- substituteC subst ty
    return $ IsInst cls ty'

  substituteC subst (IsEqual s t) =
    liftM2 IsEqual (substituteC subst s) (substituteC subst t)

instance CTerm ClassMethod where
  freeC (ClassMethod sig) = freeC sig
  substituteC subst (ClassMethod sig) =
    ClassMethod `liftM` substituteC subst sig

instance CTerm ClassInstance where
  freeC (AbstractClassInstance _ ts) = freeC ts
  freeC (MethodsInstance _) = return Set.empty

  substituteC subst (AbstractClassInstance v ts) =
    AbstractClassInstance v <$> substituteC subst ts

  substituteC subst inst@(MethodsInstance _) = return inst

instance CTerm TyFamilyInstance where
  freeC (TyFamilyInstance ty) = freeC ty
  substituteC subst (TyFamilyInstance ty) =
    TyFamilyInstance `liftM` substituteC subst ty

-------------------------------------------------------------------------------
-- Pretty-printing types

-- | Keep a mapping from type constructor to decorated name.
data PprNameContext =
  PprNameContext
  { pprContext :: !(PprContext HMType) 
  , tyConNames :: !(Map.Map (Ident TyCon) String)
  }

-- | A pretty-printing applicative construct for giving names to
-- anonymous variables
newtype Ppr m a = Ppr {doPpr :: IORef PprNameContext -> m a}

-- | Run a pretty-printer.  Within the scope of this pretty-printer, anonymous
-- variables will be assigned a temporary name.  The name may be different
-- between different calls to 'runPpr'.
runPpr :: NormalizeContext HMType m => Ppr m a -> m a
runPpr m = do ctx <- liftIO $ newIORef (PprNameContext initialPprContext Map.empty)
              doPpr m ctx

-- | Pretty-print a unification variable.  The caller should normalize the
--   variable before calling this function.
pprUVar :: NormalizeContext HMType m => TyVar -> Ppr m Doc
pprUVar v = Ppr $ \r -> do
  env <- liftIO $ readIORef r
  let (n, ppr_env') = getUVarName (pprContext env) v
  liftIO $ writeIORef r (env {pprContext = ppr_env'})
  return $ text n

instance Functor m => Functor (Ppr m) where
  fmap f (Ppr g) = Ppr $ \env -> fmap f (g env)

instance Applicative m => Applicative (Ppr m) where
  pure x = Ppr $ \_ -> pure x
  Ppr ff <*> Ppr xx = Ppr $ \r -> ff r <*> xx r

instance Monad m => Monad (Ppr m) where
  return x = Ppr $ \_ -> return x
  Ppr ff >>= kk = Ppr $ \r -> ff r >>= \x -> doPpr (kk x) r

instance MonadIO m => MonadIO (Ppr m) where liftIO m = Ppr $ \_ -> liftIO m

instance MonadTrans Ppr where
  lift m = Ppr $ \_ -> m

outer_prec = 0
rel_prec = 1                    -- Relations on types
arrow_prec = 2                  -- Function arrows
prod_prec = 3                   -- Products in function domains
app_prec = 4                    -- Application

-- | Pretty-print a type constructor
pprTyCon :: MonadIO m => TyCon -> Ppr m Doc
pprTyCon c = Ppr $ \r -> do
  env <- liftIO $ readIORef r
  let (env', decorated_name) = get_decorated_name env
  liftIO $ writeIORef r env'
  return $ text decorated_name
  where
    -- To avoid name collisions, allocate a name that doesn't match any 
    -- previously used names
    get_decorated_name env
      | Just name <- Map.lookup (tyConID c) (tyConNames env) =
          (env, name)
      | otherwise =
          let (name', ppr_env') = decorateName (pprContext env) (showTyCon c)
              names' = Map.insert (tyConID c) name' (tyConNames env)
          in (PprNameContext ppr_env' names', name')

-- | Pretty-print a type
pprType :: NormalizeContext HMType m => HMType -> Ppr m Doc
pprType ty = prType Nothing outer_prec ty 

-- | Pretty-print a predicate 
pprPredicate :: NormalizeContext HMType m => Predicate -> Ppr m Doc
pprPredicate (IsInst con ty) =
  appExpr outer_prec <$> pprTyCon con
                     <*> fmap return (prType Nothing app_prec ty)

pprPredicate (IsEqual t1 t2) =
  eqExpr outer_prec <$> prType Nothing app_prec t1
                    <*> prType Nothing app_prec t2

pprConstraint :: NormalizeContext HMType m => Constraint -> Ppr m Doc
pprConstraint xs = fsep . punctuate comma <$> traverse pprPredicate xs

pprQualified :: NormalizeContext HMType m => (a -> Ppr m Doc) -> Qualified a
             -> Ppr m Doc
pprQualified p (Qualified params cst x) = do
  params' <- mapM pprTyCon params
  cst' <- pprConstraint cst
  x' <- p x
  let params_doc = if null params'
                   then empty
                   else text "forall" <+> hsep params' <> text "."
      cst_doc = if null cst
                then empty
                else cst' <+> text "=>"
      doc = params_doc <+> sep [cst_doc, x']
  return doc

pprTyScheme = pprQualified pprType

pprInstance :: NormalizeContext HMType m => (a -> Ppr m Doc) -> Instance a
            -> Ppr m Doc
pprInstance p (Instance head body) = do
  head_doc <- pprType head
  body_doc <- p body
  return $ head_doc <+> text "|->" <+> body_doc

pprTyFamilyInstance (TyFamilyInstance t) = pprType t

pprClassMethods :: NormalizeContext HMType m => [ClassMethod] -> Ppr m Doc
pprClassMethods ms = fmap (braces . vcat . punctuate comma) $
                     mapM pprClassMethod ms

pprClassMethod (ClassMethod scm) = pprQualified pprType scm

pprClassInstance (AbstractClassInstance v ts) = do
  ts' <- mapM (prType Nothing app_prec) ts
  let ts_doc = if null ts'
               then empty
               else text "with" <+> sep ts'
  return $ text "Abstract instance" <+> text (show v) <+> ts_doc

pprClassInstance (MethodsInstance vs) =
  return $ braces $ fsep $ punctuate comma $ map (text . show) vs

pprTypeBinding :: NormalizeContext HMType m => TypeBinding -> Ppr m Doc
pprTypeBinding binding =
  case binding
  of TyVarAss ->
       return $ text "TyVar"

     TyConAss dt ->
       return $ text "TyCon" <+> text (show $ dtBoxed dt)

     TyClsAss cls -> do
       let tycon = text (show $ clsTyCon cls)
           dict_con = text (show $ clsSFDictCon cls)
       signature <- pprQualified pprClassMethods $ clsSignature cls
       instances <- mapM (pprQualified (pprInstance pprClassInstance)) $ clsInstances cls
       return $ text "TyCls" <+> (tycon <> comma <+> dict_con $$
                                  signature $$
                                  vcat instances)

     TyFunAss fam -> do
       let arity = text $ show $ tfArity fam
           kind = text $ showKind $ tfKind fam
       instances <- mapM (pprQualified (pprInstance pprTyFamilyInstance)) $
                    tfInstances fam
       return $ text "TyFun" <+> (parens arity <+> kind $$ vcat instances)

pprTypeEnvironment :: NormalizeContext HMType m =>
                      Map.Map TyCon TypeBinding -> Ppr m Doc
pprTypeEnvironment m = do
  assocs <- forM (Map.toList m) $ \(c, b) -> do
    c_doc <- pprTyCon c
    b_doc <- pprTypeBinding b
    return $ hang (c_doc <+> text "|->") 12
             (text (showKind $ tyConKind c) $$ b_doc)
  return $ vcat assocs

pprDataCon :: NormalizeContext HMType m => DataCon -> Ppr m Doc
pprDataCon (DataCon sig) = pprTyScheme function_sig
  where
    -- Create a function type from the type signature
    function_sig = do (tys, FOConstructor tycon) <- sig
                      let range = ConTy tycon `appTys` map ConTy (qParams sig)
                      return $ functionTy tys range

pprValueBinding :: NormalizeContext HMType m => ValueBinding -> Ppr m Doc
pprValueBinding binding =
  case binding
  of PolyVarAss scm -> do
       scm <- pprTyScheme scm
       return $ text "PolyVar" <+> scm
     MonoVarAss ty -> do
       ty <- pprType ty
       return $ text "MonoVar" <+> ty
     RecVarAss _ ->
       return $ text "RecVar"
     DataConAss dc -> do
       dc_doc <- pprDataCon dc
       return $ text "DataCon" <+> dc_doc
     MethodAss cls_tycon index -> do
       tycon <- pprTyCon cls_tycon
       return $ text "Method" <+> tycon <+> text (show index)

pprValueEnvironment :: NormalizeContext HMType m =>
                       Map.Map Variable ValueBinding -> Ppr m Doc
pprValueEnvironment m = do
  assocs <- forM (Map.toList m) $ \(v, b) -> do
    let c_doc = pprVariable v
    b_doc <- pprValueBinding b
    return $ hang (c_doc <+> text "|->") 12 b_doc
  return $ vcat assocs
  
prType :: NormalizeContext HMType m =>
          Maybe Int             -- ^ Fuel, to limit maximum nesting depth
       -> Int                   -- ^ Precedence
       -> HMType                -- ^ Type
       -> Ppr m Doc             -- ^ Printer of the type
prType (Just 0) _ _ = pure $ text "..." 

prType fuel prec ty = lift (uncurryApp ty) >>= pr
  where
    pr (op, args) = 
      case op
      of VarTy v -> app (pprUVar v) args
         ConTy c -> app (pprTyCon c) args
         FunTy n
           | n + 1 == length args -> fun (init args) (last args)
           | otherwise -> app (pure $ fun_constructor n) args
         TupleTy n
           | n == length args -> tuple args
           | otherwise -> app (pure $ tuple_constructor n) args

         AnyTy k -> pure $ any_constructor k

         -- 'AppTy', 'TFunAppTy' should not appear after uncurrying
         _ -> internalError "prType"

    continue prec t = prType (fmap (subtract 1) fuel) prec t

    app mk_op args = appExpr prec <$> mk_op
                                  <*> traverse (continue app_prec) args
    fun [] rng  = funExpr prec <$> pure ([text "()"])
                               <*> continue arrow_prec rng
    fun dom rng = funExpr prec <$> traverse (continue prod_prec) dom
                               <*> continue arrow_prec rng
    tuple ts = tupleExpr <$> traverse (continue outer_prec) ts

    -- Expression-building expressions
    fun_constructor n = parens $ text ("FunTy " ++ show n)
    tuple_constructor n = parens $ text ("TupleTy " ++ show n)
    any_constructor k = parens $ text ("AnyTy " ++ showKind k)

appExpr p op []   = op
appExpr p op args = parenthesize p app_prec $ sep (op : args)

eqExpr p t1 t2 = parenthesize p rel_prec $ sep [t1, text "~", t2]

funExpr p dom rng = let dom_doc = sep $ intersperse (text "*") dom
                        fun_doc = sep [dom_doc, text "->", rng]
                    in parenthesize p arrow_prec fun_doc

tupleExpr xs = parens $ sep $ punctuate comma xs

parenthesize context_prec expr_prec doc
  | context_prec >= expr_prec = parens doc
  | otherwise = doc
