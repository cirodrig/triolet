{-| Proof derivation.
-}

{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}
module Untyped.Proof
       (ProofBinding,
        pprProofBinding,
        ProofEnvironment(..),
        PE,
        liftTE_PE,
        getPlaceholders_PE,
        placeholderFree_PE,
        generateProof,
        lookupEvidence,
        prove,
        proofExp,
        assumeConstraint,
        mkProofBinding,
        assumeProofBinding,
        satisfyPlaceholders,
        satisfyPlaceholder)
where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Trans
import Data.IORef
import Data.List
import Data.Maybe
import Data.Function
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ 

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.SourcePos
import Common.Supply
import Untyped.Classes
import Untyped.Instantiation
import Untyped.Kind
import Untyped.TIExp
import Untyped.TIExpConstructors
import Untyped.TIMonad
import Untyped.Builtins2
import Untyped.Variable
import qualified SystemF.Syntax as SF
import qualified Builtins.Builtins as SF
import Untyped.Type
import Untyped.TypeUnif
import Untyped.Unif
import Type.Level
import Type.Var as SF
import Globals

type ProofBinding = (Predicate, TIPat)

pprProofBinding :: NormalizeContext HMType m => ProofBinding -> Ppr m Doc
pprProofBinding (p, TIVarP v _) = do
  p_doc <- pprPredicate p
  let v_doc = SF.pprVar v
  return $ v_doc <+> colon <+> p_doc

-- | A proof environment assigns proof values to predicates.
-- Instance predicates are assigned class dictionary values.
data ProofEnvironment =
  ProofEnvironment
  { -- | A list associating proof values to predicates.
    --   For each @(p, v)@ in the list, @v@ holds the proof of @p@.
    envProofValues :: [(Predicate, SF.Var)]

    -- | An expression builder.  This builds a sequence of let-expressions 
    --   expression that bind all proof values to variables.
    --   The two arguments are an expression
    --   that uses the proof values, and its representation.
  , envProofExp :: TIExp -> TIExp
  }

emptyProofEnvironment :: ProofEnvironment
emptyProofEnvironment = ProofEnvironment [] id

-- | A monad for creating proofs.
--
--   The monad builds an expression containing proof values and
--   constructing a proof expression.
--   New placeholders may be created.
newtype PE a = PE {unPE :: RWST Environment Placeholders ProofEnvironment IO a}

instance Functor PE where
  fmap f (PE m) = PE (fmap f m)

instance Applicative PE where
  pure x = PE (pure x)
  PE f <*> PE x = PE (f <*> x)

instance Monad PE where
  return x = PE (return x)
  PE m >> PE k = PE (m >> k)
  PE m >>= k = PE (m >>= unPE . k)

instance MonadIO PE where liftIO m = PE (liftIO m)

instance UMonad HMType PE where freshUVarID = liftIO freshTyVarID

instance EnvMonad PE where
  getEnvironment = PE ask
  getsEnvironment f = PE (asks f)
  withEnvironment f (PE m) = PE $ local f m

instance Supplies PE (Ident SF.Var) where
  fresh = do env <- getEnvironment
             liftIO $ supplyValue $ envSFVarIDSupply env

liftTE_PE :: TE a -> PE a
liftTE_PE (TE m) = PE $ RWST $ \r s -> do
  x <- runReaderT m r
  return (x, s, mempty)

-- If 'Nothing' is returned, then discard side effects
dropEffectsOnFailure :: PE (Maybe a) -> PE (Maybe a)
dropEffectsOnFailure (PE m) = PE $ RWST $ \r s -> do
  (x, s', w) <- runRWST m r s
  case x of
    Nothing -> return (Nothing, s, mempty)
    Just _  -> return (x, s', w)

-- | Generate proof terms in the context of an expression.  Add the
--   proof-generating code to the expression.
generateProof :: PE (TIExp, a) -> TI (TIExp, a)
generateProof (PE m) = TI $ RWST $ \r s -> do
  ((user_exp, x), proof_env, placeholders) <-
    runRWST m r emptyProofEnvironment
  let exp = envProofExp proof_env user_exp
  return ((exp, x), (), ([], placeholders, []))

-- | Create a dictionary placeholder
mkDictPlaceholder_PE :: Predicate -> PE Placeholder
mkDictPlaceholder_PE prd = do
  ref <- liftIO $ newIORef Nothing
  let ph = DictPlaceholder $ DictP prd ref
  deferPlaceholder_PE ph
  return ph

-- | Defer the resolution of a placeholder.
deferPlaceholder_PE :: Placeholder -> PE ()
deferPlaceholder_PE ph = PE $ tell [ph]
-- | Extract the placeholders produced by the argument.
--   The placeholders are cleared.
getPlaceholders_PE :: PE a -> PE (a, Placeholders)
getPlaceholders_PE (PE m) = PE (censor (const mempty) $ listen m)

-- | Raise an exception if the computation creates placeholders.
--   The string is a human-readable description of the program location for
--   error reporting.
placeholderFree_PE :: String -> PE a -> PE a
placeholderFree_PE location (PE m) = PE $ do
  (x, p) <- listen m
  if null (p :: Placeholders)
    then return x
    else internalError $ "New placeholders may not be created in " ++ location

getProofs :: PE [(Predicate, SF.Var)]
getProofs = PE (gets envProofValues)

-- | Create a proof value from a witness variable
proofExp :: Predicate           -- ^ The predicate witnessed by the varible
         -> SF.Var              -- ^ A witness
         -> TIExp               -- ^ A proof value
proofExp p v = mkVarE noSourcePos (predicateRepr p) v

-- | Get all predicates that have been proven
getProofContext :: PE Constraint
getProofContext = PE (gets $ map fst . envProofValues)

-- | Add a proof to the proof environment.  Return a witness variable.
--   The proof-constructing expression is appended to any expressions
--   that have already been added.
insertProof :: Predicate -> TIExp -> PE SF.Var
insertProof prd proof_exp = do
  proof_var <- SF.newAnonymousVar ObjectLevel
  PE $ modify (insert_proof proof_var)
  return proof_var
  where
    insert_proof proof_var (ProofEnvironment env mk_exp) =
      let env' = (prd, proof_var) : env
          proof_type = mkPredicate prd
          var_binder = TIVarP proof_var proof_type
          mk_exp' body =
            mk_exp $
            mkLetE noSourcePos var_binder proof_exp body
      in ProofEnvironment env' mk_exp'

-- | Add an evidence variable to the proof environment.
insertEvidence :: Predicate -> SF.Var -> PE ()
insertEvidence prd proof_var = PE $ modify (insert_proof proof_var)
  where
    insert_proof proof_var (ProofEnvironment env mk_exp) =
      let env' = (prd, proof_var) : env
      in ProofEnvironment env' mk_exp

-- | Add some code to the proof environment
insertCode :: (TIExp -> TIExp) -> PE ()
insertCode mk_code = PE $ modify ins
  where
    ins (ProofEnvironment env mk_exp) =
      ProofEnvironment env (mk_exp . mk_code)

-- | Look up a proof of a predicate in the proof environment.
lookupEvidence :: Predicate -> PE (Maybe Var)
lookupEvidence prd = do
  m_result <- findM match_proof =<< getProofs
  return $! case m_result
            of Just (_, v) -> Just v
               Nothing -> Nothing
  where
    match_proof (p, v) = predicatesEqual prd p

-- | Generate or look up a proof of a predicate.
--   If successful, return the evidence and any unresolvable subgoals.
--   Otherwise, return 'Nothing'.
prove :: Predicate -> PE (Maybe (SF.Var, Constraint))
prove prd = debug $ do
  m_prf <- lookupEvidence prd
  case m_prf of
    Just v  -> return $ Just (v, [])
    Nothing -> createProof prd
  where
    debug m = do
      proofs <- getProofs
      message <- runPpr $ do
        prd_doc <- pprPredicate prd
        ctx_doc <- pprConstraint $ map fst proofs
        return $ text "Proving" <+> prd_doc $$ text "Given" <+> ctx_doc
      liftIO $ print message
      m

{-proveConstraint :: Constraint -> PE (Maybe ([TIExp], Constraint))
proveConstraint cst = dropEffectsOnFailure $ go cst
  where
    go (p:cst) = do
      m_proof <- prove p
      case m_proof of
        Nothing -> return Nothing
        Just (e, cst1) -> do
          m_proofs <- proveConstraint cst
          case m_proofs of
            Nothing -> return Nothing
            Just (es, cst2) ->
              return $ Just (e:es, cst1 ++ cst2)

    go [] = return $ Just ([], [])-}

-- | Create a new proof of a predicate.
createProof :: Predicate -> PE (Maybe (SF.Var, Constraint))
createProof prd = dropEffectsOnFailure $ do
  -- Rewrite constraint to normalized form
  context <- getProofContext
  -- FIXME: Must simplify context so it is confluent & terminating
  (change1, prd') <- liftTE_PE $ normalizePredicate context prd
  liftIO . print . (text "using context" <+>) =<< runPpr (pprConstraint context)
  liftIO . print . (text "normalized predicate to" <+>) =<< runPpr (pprPredicate prd)

  -- Simplify the predicate to HNF.  Check whether simplification occurred.
  m_proof <- toHnf noSourcePos prd'  
  (change2, proof, cst') <-
    case m_proof
    of Just (proof, cst') -> return (True, proof, cst')
       Nothing -> do
         hyp <- hypothesis prd'
         return (False, hyp, [prd'])

  -- DEBUG
  {-message <- runPpr $ do
    old <- pprPredicate prd
    new <- pprConstraint cst'
    return $ text "reduced" <+> old <+> text "to" <+> new
  liftIO $ print message-}

  -- If rewriting was performed, generate a coercion term
  proof' <-
    if change1
    then coerceDerivation prd' prd proof
    else return proof

  if change1 || change2
    then return $ Just (proof', cst')
    else return Nothing

instance Derivation PE SF.Var where
  liftTE _ m = liftTE_PE m

  hypothesis prd = do
    -- Create a placeholder for this hypothesis
    liftIO . print . (text "New hypothesis" <+>) =<< runPpr (pprPredicate prd) -- DEBUG
    ph <- mkDictPlaceholder_PE prd
    -- Assign its result to a variable
    saveTerm prd $ PlaceholderTE ph

  lookupDerivation = lookupEvidence

  instanceDerivation p i c_t c_p i_t i_p =
    instanceTerm p i c_t c_p i_t i_p >>= saveTerm p

  boxedReprDerivation p = boxedReprTerm p >>= saveTerm p

  equalityDerivation p = equalityTerm p >>= saveTerm p

  coerceDerivation p1 p2 d = coerceTerm p1 p2 d >>= saveTerm p2

  magicDerivation p = magicTerm p >>= saveTerm p

  superclassDerivation cls ty d = do
    superclasses <- getSuperclasses cls ty d

    -- Add dictionaries to proof environment
    sequence_ [insertEvidence p v | (v, p) <- superclasses]

    return [(p, v) | (v, p) <- superclasses]

saveTerm :: Predicate -> TIExp -> PE SF.Var
saveTerm p d = do
  liftIO . print =<< liftM (text "save" <+>) (runPpr $ pprPredicate p)
  insertProof p d

instanceTerm :: Predicate              -- ^ Derived predicate
             -> Instance ClassInstance -- ^ Instance satisfying the predicate
             -> [HMType]               -- ^ Class type arguments
             -> [(Predicate, SF.Var)]  -- ^ Class premises
             -> [HMType]               -- ^ Instance type arguments
             -> [(Predicate, SF.Var)]  -- ^ Instance premises
             -> PE TIExp
instanceTerm prd@(IsInst tycon inst_type) inst c_ty_args c_premises
             i_ty_args i_premises = do
  -- Construct a dictionary
  Just cls <- getTyConClass tycon
  liftIO $ putStrLn ("instanceTerm " ++ show (length c_premises) ++ " " ++ show (length i_premises)) -- DEBUG
  case instBody inst of
    AbstractClassInstance fun type_args ->
      -- Create a function call
      return $ instantiate type_args fun

    MethodsInstance methods ->
      -- Create a class dictionary
      let inst_methods = map (instantiate i_ty_args) methods
          c_premise_exps = map (uncurry proofExp) c_premises
      in return $ mkDictE noSourcePos cls (mkType inst_type)
                  c_premise_exps inst_methods
  where
    -- Instantiate a function or class method.
    -- For class methods, the type arguments are given by the instance's
    -- type signature; for abstract instances, they are given explicitly.
    instantiate type_args f_var =
      let fun_ty_args = map mkType type_args
          fun_args = map (uncurry proofExp) i_premises
          fun_repr = polyThingRepr TIBoxed type_args fun_args
          fun = mkVarE noSourcePos fun_repr f_var
      in mkPolyCallE noSourcePos TIBoxed fun fun_ty_args fun_args

instanceTerm _ _ _ _ _ _ = internalError "instanceTerm: Not a class instance"

boxedReprTerm :: Predicate -> PE TIExp
boxedReprTerm prd@(IsInst tycon inst_type) =
  let dict = mkVarE noSourcePos TIBoxed (SF.coreBuiltin SF.The_repr_Box)
  in return $ mkPolyCallE noSourcePos TIBoxed dict [mkType inst_type] []

equalityTerm :: Predicate -> PE TIExp
equalityTerm prd@(IsEqual t1 t2) =
  -- Call 'unsafeMakeCoercion' to create a coercion term
  let f = mkVarE noSourcePos TIUncoercedVal (SF.coreBuiltin SF.The_unsafeMakeCoercion)
  in return $ mkPolyCallE noSourcePos TIUncoercedVal f [mkType t1, mkType t2] []

coerceTerm :: Predicate -> Predicate -> SF.Var -> PE TIExp
coerceTerm src_type result_type src =
  return $ mkCoerceE noSourcePos TIBoxed
           (mkPredicate src_type) (mkPredicate result_type) (proofExp src_type src)

magicTerm :: Predicate -> PE TIExp
magicTerm result_type =
  let f = mkVarE noSourcePos TIBoxed (SF.coreBuiltin SF.The_fun_undefined)
  in return $ mkPolyCallE noSourcePos TIBoxed f [mkPredicate result_type] []

-- | Get the superclass dictionaries from a class dictionary
getSuperclasses :: TyCon -> HMType -> SF.Var -> PE [(SF.Var, Predicate)]
getSuperclasses cls_con ty dict = do
  Just cls <- getTyConClass cls_con

  -- If there are no superclasses, don't generate any code
  if clsIsAbstract cls || null (qConstraint $ clsSignature cls)
    then return []
    else do
      -- Instantiate the class to get its superclass constraints
      InstanceType _ constraint c_methods <- instantiateClass cls ty

      -- Extract the class fields
      let dict_exp = proofExp (IsInst cls_con ty) dict
      (mk_case, superclasses, _) <-
        mkCaseOfDict noSourcePos cls ty constraint c_methods dict_exp
      insertCode mk_case
      return $ zip superclasses constraint

-- | Add a constraint to the environment.  For each predicate in the
--   constraint, a new variable is created.  The constraints are assumed 
--   to be true; their evidence must be supplied by binding the variables 
--   in the context of the proof term.
assumeConstraint :: Constraint -> PE [ProofBinding]
assumeConstraint cst = mapM assumePredicate cst

assumePredicate :: Predicate -> PE ProofBinding
assumePredicate prd = do
  -- Create a variable to hold the evidence
  v <- SF.newAnonymousVar ObjectLevel
  assumePredicate' prd v

assumePredicate' prd v = do
  -- Add evidence to the environment
  insertEvidence prd v

  -- Add superclass proofs to environment
  assumeSuperclasses prd v
      
  let pattern = mkVarP v (mkPredicate prd)
  return (prd, pattern)

-- | Create a proof binding, but don't add it to the type environment.
--   The binding should be added by 'insertProofBinding'.
mkProofBinding :: Predicate -> TE ProofBinding
mkProofBinding prd = do
  v <- SF.newAnonymousVar ObjectLevel
  let proof_exp = mkVarP v (mkPredicate prd)
  return (prd, proof_exp)

assumeProofBinding :: ProofBinding -> PE ()
assumeProofBinding (prd, pattern@(TIVarP v _)) = do
  -- Add evidence to the environment
  insertEvidence prd v

  -- Add superclass proofs to environment
  assumeSuperclasses prd v

-- | Add the given class's superclass constraints to the environment
assumeSuperclasses :: Predicate -> SF.Var -> PE ()
assumeSuperclasses (IsInst tycon ty) dict = do
  superclasses <- superclassDerivation tycon ty dict
  mapM_ (uncurry assumeSuperclasses) superclasses

assumeSuperclasses (IsEqual _ _) _ = return ()

-- | Attempt to satisfy a list of placeholders from the current proof
--   environment.  Return residual constraints produced by placeholder 
--   satisfaction.  Unsatisfied placeholders are deferred.
satisfyPlaceholders :: Placeholders -> PE Constraint
satisfyPlaceholders phs = mconcat `liftM` mapM satisfy_placeholder phs
  where
    satisfy_placeholder p = do
      m_residual <- satisfyPlaceholder p
      case m_residual of
        Nothing  -> deferPlaceholder_PE p >> return []
        Just cst -> return cst

-- | Attempt to satisfy a placeholder from the current proof environment.
--   Return residual constraints if placeholder is satisfied,
--   'Nothing' otherwise.
satisfyPlaceholder :: Placeholder -> PE (Maybe Constraint)
satisfyPlaceholder (RecVarPlaceholder _) = return Nothing
satisfyPlaceholder (DictPlaceholder ph) = satisfyDictPlaceholder ph

satisfyDictPlaceholder ph =
  -- If placeholder has already been assigned, no need to do anything more
  ifM (liftIO $ isDictPSet ph) (return (Just [])) $ do

    -- Create a proof term for this placeholder
    m_prf <- prove $ dictPPredicate ph
    case m_prf of
      Nothing -> return Nothing
      Just (evidence, residual) -> do
        liftIO $ setDictP ph evidence
        return $ Just residual
