{-| Helper routines to convert from untyped code to System F code.
--
-- Type inference converts each untyped expression to a temporary /extended/
-- System F representation that is defined in this file.  In the extended
-- representation, a type is represented by an @IO@ action that evaluates to
-- the actual type; this action is only evaluated after all unification has
-- been performed, and reads the final value of unified variables.  Expressions
-- are extended with placeholders for type class code, which are assigned after
-- the relevant class is resolved.  The extended representation is converted to
-- regular System F after type inference completes.
-- 
-}

{-# LANGUAGE FlexibleInstances, DeriveDataTypeable #-}
module Untyped.GenSystemF where

import Prelude hiding(mapM, sequence)
import Control.Applicative
import Control.Concurrent.MVar
import Control.Monad hiding(forM, mapM, sequence)
import Data.Function
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Data.Traversable
import Data.Typeable(Typeable)
import qualified Data.Map as Map
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.MonadLogic
import Common.SourcePos
import Common.Supply
import Globals
import Export
import Untyped.HMType
import Untyped.Kind
import Untyped.Unification
import Untyped.Data
import {-# SOURCE #-} Untyped.Classes
import qualified Untyped.Syntax as Untyped
import qualified SystemF.Syntax as SystemF
import SystemF.Syntax(ExpInfo, mkExpInfo)
import qualified Builtins.Builtins as SystemF
import Type.Var
import qualified Type.Type
import Type.Level

debugPlaceholders = False

-------------------------------------------------------------------------------
-- Type schemes

instance Type TyScheme where
  freeTypeVariables (TyScheme qvars cst ty) = do
    -- All variables in the constraint must also be mentioned in the type,
    -- so it's not necessary to scan the constraint 
    fv <- freeTypeVariables ty
    return $ fv Set.\\ Set.fromList qvars

-- | Convert a first-order type to a monomorphic type scheme
monomorphic :: HMType -> TyScheme
monomorphic t = TyScheme [] [] t

-- | Create a type scheme with some type parameters
forallType :: [Kind] -> ([TyCon] -> (Constraint, HMType)) -> IO TyScheme
forallType kinds f = do
  qvars <- forM kinds $ \k -> newTyVar k Nothing
  
  -- This must be lazy, because it's used when creating classes and the
  -- constraint may refer to a class
  return $ case f qvars
           of (cst, ty) -> TyScheme qvars cst ty

-- | Instantiate a type scheme by giving fresh names to all type variables
instantiate :: TyScheme -> IO (TyVars, Constraint, HMType)
instantiate (TyScheme qvars cst ty) = do
  -- Create a substitution from each qvar to a new variable 
  new_qvars <- mapM duplicateTyVar qvars
  let substitution = substitutionFromList $ zip qvars $ map ConTy new_qvars

  -- Apply the substitution to the type
  ty' <- rename substitution ty
  cst' <- mapM (rename substitution) cst

  return (new_qvars, cst', ty')

-- | Instantiate a class method's type scheme. 
--   Class methods have a class parameter and class constraint in addition
--   to instance's type scheme.
--
--   The returned tuple contains the instantiated class variable, the
--   instantiated class constraint, the class predicate,
--   the instantiated method type parameters,
--   the instantiated method constraint, and the instantiated method type.
instantiateClassMethod :: Class
                       -> TyScheme
                       -> IO (TyCon, Constraint, Predicate, TyVars, Constraint, HMType)
instantiateClassMethod cls (TyScheme qvars cst ty) = do
  -- Create a substitution from each qvar to a new variable
  let cls_sig = clsSignature cls
  new_c_qvar <- duplicateTyVar $ clsParam cls_sig
  new_m_qvars <- mapM duplicateTyVar qvars
  let substitution =
        substitutionFromList $
        (clsParam cls_sig, ConTy new_c_qvar) : zip qvars (map ConTy new_m_qvars)

  -- Apply the substitution to the type
  ty' <- rename substitution ty
  c_cst' <- mapM (rename substitution) $ clsConstraint cls_sig
  m_cst' <- mapM (rename substitution) cst

  return (new_c_qvar, c_cst', ConTy new_c_qvar `IsInst` cls,
          new_m_qvars, m_cst', ty')

-- | Instantiate a type scheme and match it to some other type.
-- Throw an error if types do not match.
instantiateAs :: SourcePos -> TyScheme -> HMType -> IO ([HMType], Constraint)
instantiateAs pos scheme ty = do
  (qvars, cst, head) <- instantiate scheme
  cst2 <- unify pos head ty
  return (map ConTy qvars, cst2 ++ cst)

-- | Apply a substitution to a type scheme.  The substitution must only
-- mention free variables of the type scheme.
renameTyScheme :: Substitution -> TyScheme -> IO TyScheme
renameTyScheme sub (TyScheme qvars cst fot) = do
  cst' <- mapM (rename sub) cst
  fot' <- rename sub fot
  return $ TyScheme qvars cst' fot'

-------------------------------------------------------------------------------
-- Type classes

instance Eq Class where
  (==) = (==) `on` (clsName . clsSignature)

instance Eq TyFamily where
  (==) = (==) `on` (clsName . tfSignature)

-- | Construct a type scheme representing all types covered by this instance
insScheme :: Instance -> TyScheme
insScheme i = insSigScheme (insSignature i)

insSigScheme i = TyScheme (insQVars i) (insConstraint i) (insType i)

instance Type Predicate where
  freeTypeVariables (IsInst t _) = freeTypeVariables t
  freeTypeVariables (IsEqual t1 t2) =
    liftM2 Set.union (freeTypeVariables t1) (freeTypeVariables t2)

instance Type [Predicate] where
  freeTypeVariables xs = liftM Set.unions $ mapM freeTypeVariables xs

-- | During unification, predicates are only considered equal if
-- they are exactly equal.  Other identities are taken care of during context
-- reduction.
instance Unifiable Predicate where
  uShow (t `IsInst` c) = display <$> uShow t
    where
      display doc = text (clsName $ clsSignature c) <+> parens doc

  uShow (IsEqual t1 t2) = do 
    t1_doc <- uShow t1
    t2_doc <- uShow t2
    return $ t1_doc <+> text "~" <+> t2_doc

  rename s (IsInst t c) = do 
    t' <- rename s t
    return $ IsInst t' c

  rename s (IsEqual t1 t2) = do
    t1' <- rename s t1
    t2' <- rename s t2
    return $ IsEqual t1' t2'

  unify pos p1 p2 =
    case (p1, p2)
    of (IsInst t1 c1, IsInst t2 c2)
         | c1 == c2 -> unify pos t1 t2
  
       _ -> fail "Cannot unify predicates"
  
  matchSubst subst p1 p2 =
    case (p1, p2)
    of (IsInst t1 c1, IsInst t2 c2)
         | c1 == c2 -> matchSubst subst t1 t2

       (IsEqual _ _, IsEqual _ _) ->
         internalError "match: Not implemented for type families"
       
       _ -> return Nothing
  
  uEqual p1 p2 =
    case (p1, p2)
    of (IsInst t1 c1, IsInst t2 c2)
         | c1 == c2 -> uEqual t1 t2
       (IsEqual s1 t1, IsEqual s2 t2) ->
         uEqual s1 s2 >&&> uEqual t1 t2
       _ -> return False

isIdDerivation :: Derivation -> Bool
isIdDerivation (IdDerivation {}) = True
isIdDerivation _ = False

-- | A proof environment assigns proof values to predicates.
-- Instance predicates are assigned class dictionary values.
newtype ProofEnvironment =
  ProofEnvironment 
  { envProofs     :: [(Predicate, TIExp)]
  }

-- | Look up the proof of a predicate in an environment
lookupProof :: Predicate -> ProofEnvironment -> IO (Maybe TIExp)
lookupProof prd env = do
  assoc <- findM ((prd `uEqual`) . fst) $ envProofs env
  return $ fmap snd assoc

-- | Render the proofs in a proof environment (for debugging)
pprProofEnvironment :: ProofEnvironment -> Ppr Doc
pprProofEnvironment env = do
  pfs <- mapM uShow $ map fst $ envProofs env
  return $ vcat $ punctuate semi pfs

instance Monoid ProofEnvironment where
  mempty = ProofEnvironment []
  ProofEnvironment p1 `mappend` ProofEnvironment p2 =
    ProofEnvironment (p1 ++ p2)

-------------------------------------------------------------------------------
-- Type inference System F data structures

isPlaceholderExp :: Placeholder -> Bool
isPlaceholderExp (RecVarPH {}) = True
isPlaceholderExp (DictPH {}) = True
isPlaceholderExp _ = False

isResolved :: Placeholder -> IO Bool
isResolved ph 
  | isPlaceholderExp ph =
      return . not =<< isEmptyMVar (phExpResolution ph)
  | otherwise =
      internalError "Not a placeholder"

setPlaceholderElaboration :: Placeholder -> TIExp -> IO ()
setPlaceholderElaboration ph exp 
  | isPlaceholderExp ph = do
      b <- isEmptyMVar (phExpResolution ph)
      unless b $ internalError "Placeholder is already resolved"
      putMVar (phExpResolution ph) exp
  | otherwise = internalError "Not a placeholder"

delayType :: Type.Type.Type -> TIType
delayType t = DelayedType (return t)

mkWildP :: TIType -> TIPat
mkWildP ty = TIWildP ty

mkVarP :: Var -> TIType -> TIPat
mkVarP v ty = TIVarP v ty

mkTupleP :: [TIPat] -> TIPat
mkTupleP fs = TITupleP fs

mkVarE :: SourcePos -> Var -> TIExp
mkVarE pos v = VarTE (mkExpInfo pos) v

mkConE :: SourcePos -> Var -> [TIType] -> [TIType] -> [TIExp] -> TIExp
mkConE pos c ty_args ex_types fields =
  let con = TIConInst c ty_args ex_types
  in ConTE (mkExpInfo pos) con fields

-- | Create the expression
--   list @n @t (fiInt @n n) (stuckBox @(arr n t) (array @t e1 e2 ...))
mkListE :: SourcePos -> TIType -> [TIExp] -> TIExp
mkListE pos elt_type elts =
  let inf = mkExpInfo pos
      n = length elts

      -- The list size as a type
      size = delayType (Type.Type.IntT $ fromIntegral n)

      -- The array type
      array_type = DelayedType $ do
        sf_elt_type <- case elt_type of DelayedType t -> t
        return $ Type.Type.varApp (SystemF.coreBuiltin SystemF.The_arr)
          [Type.Type.IntT $ fromIntegral n, sf_elt_type]

      -- Indexed integer 
      integer = mkConE pos fiint_con [size] []
                [LitTE inf (SystemF.IntL (fromIntegral n) sf_int_type)]
      -- Array expression
      array = ArrayTE inf elt_type elts
      array_box = mkConE pos (SystemF.coreBuiltin SystemF.The_stuckBox)
                  [array_type] [] [array]
  in mkConE pos (SystemF.coreBuiltin SystemF.The_make_list) [elt_type] [size]
     [integer, array_box]
  where
    sf_int_type = Type.Type.VarT (SystemF.coreBuiltin SystemF.The_int)
    fiint_con = SystemF.coreBuiltin SystemF.The_fiInt


mkLitE :: SourcePos -> Untyped.Lit -> TIExp
mkLitE pos l =
  case l
  of Untyped.IntL n      -> sf_literal $ SystemF.IntL n sf_int_type
     Untyped.FloatL n    -> sf_literal $ SystemF.FloatL n sf_float_type
     Untyped.BoolL True  -> sf_constructor SystemF.The_True
     Untyped.BoolL False -> sf_constructor SystemF.The_False
     Untyped.NoneL       -> sf_constructor SystemF.The_None
  where
    sf_literal l =
      LitTE (mkExpInfo pos) l
    sf_constructor c =
      let con = TIConInst (SystemF.coreBuiltin c) [] []
      in ConTE (mkExpInfo pos) con []

    sf_int_type = Type.Type.VarT (SystemF.coreBuiltin SystemF.The_int)
    sf_float_type = Type.Type.VarT (SystemF.coreBuiltin SystemF.The_float)

mkAppE :: SourcePos -> TIExp -> [TIType] -> [TIExp] -> TIExp
mkAppE pos oper ts args = AppTE (mkExpInfo pos) oper ts args

mkUndefinedE :: SourcePos -> TIType -> TIExp
mkUndefinedE pos ty =
  mkAppE pos (mkVarE pos (SystemF.coreBuiltin SystemF.The_fun_undefined)) [ty] []

mkCoerceE :: SourcePos -> TIType -> TIType -> TIExp -> TIExp
mkCoerceE pos from_ty to_ty e =
  CoerceTE (mkExpInfo pos) from_ty to_ty e

mkIfE :: SourcePos -> TIExp -> TIExp -> TIExp -> TIExp
mkIfE pos cond tr fa =
  let true_decon =
        TIDeConInst (SystemF.coreBuiltin SystemF.The_True) [] []
      false_decon =
        TIDeConInst (SystemF.coreBuiltin SystemF.The_False) [] []
      true_alt = TIAlt true_decon [] tr
      false_alt = TIAlt false_decon [] fa
  in CaseTE (mkExpInfo pos) cond [true_alt, false_alt]

-- | Create a call of a polymorphic function with no constraint arguments.
mkPolyCallE :: SourcePos -> TIExp -> [TIType] -> [TIExp] -> TIExp
mkPolyCallE pos oper [] [] = oper
mkPolyCallE pos oper ty_args args = mkAppE pos oper ty_args args

mkLetE :: SourcePos -> TIPat -> TIExp -> TIExp -> TIExp
mkLetE pos lhs rhs body = LetTE (mkExpInfo pos) lhs rhs body 

mkFunE :: SourcePos -> TIFun -> TIExp
mkFunE pos fun = LamTE (mkExpInfo pos) fun

mkLetrecE :: SourcePos -> [TIDef] -> TIExp -> TIExp
mkLetrecE pos defs body =
  LetfunTE (mkExpInfo pos) (SystemF.Rec defs) body

mkDictE :: SourcePos -> Class -> TIType -> [TIExp] -> [TIExp] -> TIExp
mkDictE pos cls inst_type scs methods =
  -- Apply the dictionary constructor to the instance type and all arguments
  mkConE pos (clsDictCon cls) [inst_type] [] (scs ++ methods)

-- | Get the type of a class dictionary's fields.
--
--   The fields are the superclasses and the methods.
classDictionaryFieldTypes :: Class  -- ^ Class to inspect
                          -> HMType -- ^ Type of the class instance
                          -> IO ([TIType], [TIType])
classDictionaryFieldTypes cls inst_type = do
  let cls_sig = clsSignature cls
  let instantiation = substitutionFromList [(clsParam cls_sig, inst_type)]

  -- Superclass dictionary and coercion types
  sc_types <- forM (clsConstraint cls_sig) $ \prd -> do
    liftM convertPredicate $ rename instantiation prd

  -- Method types
  m_types <- forM (clsMethods cls) $ \method -> do
    liftM convertTyScheme $ renameTyScheme instantiation (clmSignature method)

  return (sc_types, m_types)

-- | Create an expression to deconstruct a class dictionary.
--
--   The fields of the class dictionary are bound to variables that may be
--   used to construct the body.
mkCaseOfDict :: forall a.
                SourcePos
             -> Class           -- ^ The class whose dictionary is being used
             -> HMType          -- ^ The class instance's type
             -> TIExp           -- ^ The class dictionary expression
             -> IO (([Var] -> [Var] -> IO (TIExp, a)) -> IO (TIExp, a))
mkCaseOfDict pos cls inst_type dict = do
  (sc_types, m_types) <- classDictionaryFieldTypes cls inst_type

  -- Create anonymous parameter variables
  sc_vars <- replicateM (length sc_types) $ do
    var_id <- withTheNewVarIdentSupply supplyValue
    return $ mkAnonymousVar var_id ObjectLevel

  m_vars <- replicateM (length m_types) $ do
    var_id <- withTheNewVarIdentSupply supplyValue
    return $ mkAnonymousVar var_id ObjectLevel

  -- Create binders for the parameters
  let mkParameter var ty = TIVarP var ty
      parameters = zipWith mkParameter sc_vars sc_types ++
                   zipWith mkParameter m_vars m_types

  let make_case_expression :: forall. ([Var] -> [Var] -> IO (TIExp, a)) -> IO (TIExp, a)
      make_case_expression make_body = do
        let ty_param = convertHMType inst_type
        (body, x) <- make_body sc_vars m_vars
        let alt = TIAlt (TIDeConInst (clsDictCon cls) [ty_param] [])
                  parameters body
            case_exp = CaseTE (mkExpInfo pos) dict [alt]
        return (case_exp, x)
  return make_case_expression
  
-- | Create an expression that selects and instantiates a class method.
-- Return the expression and the placeholders produced by instantiation.
mkMethodInstanceE :: SourcePos
                  -> Class      -- ^ Class whose method is being accessed
                  -> HMType     -- ^ The class instance's type
                  -> Int        -- ^ Index of the method to retrieve
                  -> [HMType]   -- ^ Instantiated type parameters
                  -> Constraint -- ^ Instantiated constraint
                  -> TIExp      -- ^ Dictionary expression to select from
                  -> IO (Placeholders, TIExp)
mkMethodInstanceE pos cls inst_type index ty_params constraint dict = do
  -- The class dictionary has superclass and method fields. 
  let cls_sig = clsSignature cls
      num_superclasses = length $ clsConstraint cls_sig
      num_methods = length $ clsMethods cls

  when (index >= num_methods) $
    internalError "mkMethodInstanceE: index out of range"

  -- Create a case expression that matches against the class dictionary,
  -- selects one of its fields, and instantiates the field to a monomorphic
  -- type
  make_case_expression <- mkCaseOfDict pos cls inst_type dict

  -- Select a field and instantiate it to a monotype
  let get_instance_var _ method_vars = do
        let field_expr = mkVarE pos (method_vars !! index)

        -- Instantiate the field
        (placeholders, alt_body) <-
          instanceExpression pos ty_params constraint field_expr
        return (alt_body, placeholders)

  (case_exp, placeholders) <- make_case_expression get_instance_var
  return (placeholders, case_exp)

-- | Create a placeholder for a recursive variable.  The variable is assumed
-- to have a monomorphic type, which is later generalized.
mkRecVarPlaceholder :: SourcePos
                    -> Untyped.Variable -- ^ The variable
                    -> TyCon    -- ^ Its type (a flexible type variable)
                    -> IO TIExp -- ^ Returns the created placeholder
mkRecVarPlaceholder pos variable ty = do
  tyvar <- newTyVar Star Nothing
  actual <- newEmptyMVar
  return $ RecVarPH (mkExpInfo pos) variable tyvar actual

mkDictPlaceholder :: SourcePos -> Predicate -> IO TIExp
mkDictPlaceholder pos p = do
  -- Debugging message
  when debugPlaceholders $ do
    ph_doc <- runPpr $ uShow p
    print $ text "Creating placeholder for" <+> ph_doc
  actual <- newEmptyMVar
  return $ DictPH (mkExpInfo pos) p actual

mkFunction :: SourcePos -> [TyCon] -> [TIPat] -> TIType -> TIExp
           -> IO TIFun
mkFunction pos ty_params params ret_type body = do
  ty_params' <- mapM convertTyParam ty_params
  return $ TIFun (mkExpInfo pos) ty_params' params ret_type body
  where
    convertTyParam :: TyCon -> IO TITyPat
    convertTyParam ty_param = do
      v <- tyVarToSystemF ty_param
      let k = convertKind $ tyConKind ty_param
      return $ TITyPat v k

mkExport :: SourcePos -> ExportSpec -> TIFun -> TIExport
mkExport pos spec f = TIExport pos spec f

-------------------------------------------------------------------------------
-- Conversion to System F

convertKind :: Kind -> TIType
convertKind k = delayType $ convertKind' k

-- The base kind translates to a boxed type
convertKind' Star = Type.Type.boxT
convertKind' (k1 :-> k2) = mkArrowType (convertKind' k1) (convertKind' k2)

convertHMType :: HMType -> TIType
convertHMType ty = DelayedType $ convertHMType' ty 
                   
convertHMType' ty = do
  ty' <- canonicalizeHead ty
  case ty' of
    ConTy c | isTyVar c -> do
      v <- tyVarToSystemF c
      return $ Type.Type.VarT v
            | otherwise -> do
      tyConToSystemF c
      
    -- Function types should only appear within an AppTy term
    FunTy _ -> fail "Unexpected function type constructor"

    TupleTy n ->
      return $ Type.Type.VarT $ SystemF.tupleTypeCon n

    AppTy _ _ -> do
      (operator, arguments) <- uncurryTypeApplication ty'
      arg_types <- mapM convertHMType' arguments
      case operator of
        -- Special-case function type applications
        FunTy n 
          | length arg_types == n + 1 ->
              let fun_params = init arg_types
                  fun_result = last arg_types
              in return $ mkFunctionType fun_params fun_result
          | otherwise ->
              -- This should never happen, because type inference operates on
              -- uncurried functions
              fail "Wrong number of arguments to function after type inference"
        _ -> do
          oper_type <- convertHMType' operator 
          return $ Type.Type.typeApp oper_type arg_types

    TFunAppTy op ts -> do
      sf_op <- tyConToSystemF op
      sf_ts <- mapM convertHMType' ts
      return $ Type.Type.typeApp sf_op sf_ts

    AnyTy k -> return $ Type.Type.AnyT $ convertKind' k

mkArrowType :: Type.Type.Type -> Type.Type.Type -> Type.Type.Type
mkArrowType = Type.Type.FunT

-- | Make the type of an uncurried Pyon function from @domain@ to @range@.
--
-- Depending on the calling convention indicated by the range, a stream 
-- function or action function is generated.
mkFunctionType :: [Type.Type.Type]      -- ^ domain
               -> Type.Type.Type        -- ^ range
               -> Type.Type.Type        -- ^ System F type
mkFunctionType domain range =
  foldr mkArrowType range domain

mkForallType :: Var -> Type.Type.Type -> Type.Type.Type -> Type.Type.Type
mkForallType v dom rng = Type.Type.AllT (v Type.Type.::: dom) rng

convertPredicate :: Predicate -> TIType
convertPredicate prd = DelayedType $ convertPredicate' prd 

convertPredicate' (IsInst ty cls) = do
  ty' <- convertHMType' ty
  return $ Type.Type.varApp (clsTypeCon $ clsSignature cls) [ty']

convertPredicate' (IsEqual t1 t2) = do
  -- Create a coercion value
  t1' <- convertHMType' t1
  t2' <- convertHMType' t2
  return $ Type.Type.typeApp (Type.Type.CoT Type.Type.boxT) [t1', t2']

-- | Convert a type scheme to a function type.  Each quantified variable
-- becomes a parameter in the function type.
convertTyScheme :: TyScheme -> TIType
convertTyScheme (TyScheme qvars cst ty) = DelayedType $ do
  qvars' <- mapM tyVarToSystemF qvars
  cst' <- mapM convertPredicate' cst
  ty' <- convertHMType' ty
  let constrained_type = mkFunctionType cst' ty'
      parametric_type = foldr mkFun constrained_type (zip qvars qvars')
  return parametric_type
  where
    mkFun (v, sf_v) ty =
      mkForallType sf_v (convertKind' (tyConKind v)) ty

-- | Create an instance of a polymorphic variable
--   with placeholders for all constraints
instanceExpression :: SourcePos
                   -> [HMType]   -- ^ Instantiated type parameters
                   -> Constraint -- ^ Instantiated constraint
                   -> TIExp      -- ^ Instantiated first-order expression
                   -> IO (Placeholders, TIExp) 
                      -- ^ Dictionary placeholders and instance expression
instanceExpression pos ty_params constraint exp = do
  let types = map convertHMType ty_params
  placeholders <- mapM (mkDictPlaceholder pos) constraint
  return (placeholders, mkPolyCallE pos exp types placeholders)

conInstanceExpression :: SourcePos
                      -> [HMType]   -- ^ Instantiated type parameters
                      -> Constraint -- ^ Instantiated constraint
                      -> Var        -- ^ Constructor
                      -> HMType      -- ^ Instantiated construtctor type
                      -> IO (Placeholders, TIExp)
                      -- ^ Dictionary placeholders and instance expression
conInstanceExpression pos ty_params constraint con con_type = do
  let types = map convertHMType ty_params
  placeholders <- mapM (mkDictPlaceholder pos) constraint
  exp <- eta_expand pos con types con_type
  return (placeholders, exp)
  where
    -- Eta-expand a data constructor into a System F lambda function
    eta_expand pos con types con_type = do
      (domain, range) <- expand_type con_type

      if null domain then return $ mkConE pos con types [] [] else do
        -- Create lambda function parameters
        parameter_vars <- replicateM (length domain) $ do
          var_id <- withTheNewVarIdentSupply supplyValue
          return $ mkAnonymousVar var_id ObjectLevel

        -- Create a constructor application
        let params = zipWith mkVarP parameter_vars $ map convertHMType domain
        let body = mkConE pos con types [] (map (mkVarE pos) parameter_vars)
        return $ mkFunE pos $
          TIFun (mkExpInfo pos) [] params (convertHMType range) body

    -- Expand a function type into domain and range
    expand_type t = do
      (head, operands) <- inspectTypeApplication t
      return $! case head
                of FunTy _ -> (init operands, last operands)
                   _ -> ([], t)

-- | Create an instance expression where all constraints are satisfied
-- by a proof environment
instanceExpressionWithProofs :: ProofEnvironment -- ^ A proof environment
                                                 -- supplying proofs of all
                                                 -- necessary constraints
                             -> SourcePos
                             -> [HMType]   -- ^ Instantiated type parameters
                             -> Constraint -- ^ Instantiated constraint
                             -> TIExp      -- ^ Instantiated first-order expression
                             -> IO TIExp   -- ^ Instance expression
instanceExpressionWithProofs env pos ty_params constraint exp = do
  let types = map convertHMType ty_params
  dictionaries <- mapM getProof constraint
  return $ mkPolyCallE pos exp types dictionaries
  where
    getProof prd = do
      mprf <- lookupProof prd env
      case mprf of
        Just prf -> return prf
        Nothing -> internalError "Cannot find class dictionary"

