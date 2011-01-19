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

{-# LANGUAGE TypeFamilies, EmptyDataDecls, FlexibleInstances, DeriveDataTypeable #-}
module Untyped.GenSystemF where

import Prelude hiding(mapM)
import Control.Applicative
import Control.Concurrent.MVar
import Control.Monad hiding(forM, mapM)
import Data.Function
import Data.Maybe
import qualified Data.Set as Set
import Data.Traversable
import Data.Typeable(Typeable)
import qualified Data.Map as Map
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.MonadLogic
import Gluon.Common.SourcePos
import Gluon.Common.Supply
import Gluon.Core.Level
import Gluon.Core.Builtins
import Gluon.Core(SynInfo, mkSynInfo, internalSynInfo,
                  Structure, Rec)
import Globals
import Export
import Untyped.HMType
import Untyped.Kind
import Untyped.Unification
import Untyped.Data
import qualified Untyped.Syntax as Untyped
import qualified SystemF.Syntax as SystemF
import qualified Builtins.Builtins as SystemF
import Type.Var
import qualified Type.Type

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
  return $ (new_qvars, cst', ty')

-- | Instantiate a type scheme and match it to some other type.
-- Throw an error if types do not match.
instantiateAs :: SourcePos -> TyScheme -> HMType -> IO ([HMType], Constraint)
instantiateAs pos scheme ty = do
  (qvars, cst, head) <- instantiate scheme
  unify pos head ty
  return (map ConTy qvars, cst)

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
  (==) = (==) `on` clsName

-- | Construct a type scheme representing all types covered by this instance
insScheme :: Instance -> TyScheme
insScheme i = TyScheme (insQVars i) (insConstraint i) (insType i)

instance Type Predicate where
  freeTypeVariables (IsInst t _) = freeTypeVariables t

instance Type [Predicate] where
  freeTypeVariables xs = liftM Set.unions $ mapM freeTypeVariables xs

-- | During unification, predicates are only considered equal if
-- they are exactly equal.  Other identities are taken care of during context
-- reduction.
instance Unifiable Predicate where
  uShow (t `IsInst` c) = display <$> uShow t
    where
      display doc = text (clsName c) <+> parens doc

  rename s (IsInst t c) = do 
    t' <- rename s t
    return $ IsInst t' c

  unify pos p1 p2 =
    case (p1, p2)
    of (IsInst t1 c1, IsInst t2 c2)
         | c1 == c2 -> unify pos t1 t2
  
       _ -> fail "Cannot unify predicates"
  
  match p1 p2 =
    case (p1, p2)
    of (IsInst t1 c1, IsInst t2 c2)
         | c1 == c2 -> match t1 t2
       
       _ -> return Nothing
  
  uEqual p1 p2 =
    case (p1, p2)
    of (IsInst t1 c1, IsInst t2 c2)
         | c1 == c2 -> uEqual t1 t2
       _ -> return False

isIdDerivation :: Derivation -> Bool
isIdDerivation (IdDerivation {}) = True
isIdDerivation _ = False

-- | A proof environment assigns proof values to predicates.
-- Instance predicates are assigned class dictionary values.
type ProofEnvironment = [(Predicate, TIExp)]

-- | Look up the proof of a predicate in an environment
lookupProof :: Predicate -> ProofEnvironment -> IO (Maybe TIExp)
lookupProof prd env = do
  assoc <- findM ((prd `uEqual`) . fst) env
  return $ fmap snd assoc

-- | Render the proofs in a proof environment (for debugging)
pprProofEnvironment :: ProofEnvironment -> Ppr Doc
pprProofEnvironment env = do
  docs <- mapM uShow $ map fst env
  return $ vcat $ punctuate semi docs

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

delayType :: SystemF.RType -> TIType
delayType t = DelayedType (return t)

objectSynInfo :: SynInfo
objectSynInfo = internalSynInfo ObjectLevel

synInfo :: SourcePos -> SynInfo
synInfo pos = mkSynInfo pos ObjectLevel

mkWildP :: TIType -> SystemF.Pat TI
mkWildP ty = TIWildP ty

mkVarP :: SystemF.Var -> TIType -> SystemF.Pat TI 
mkVarP v ty = TIVarP v ty

mkTupleP :: [SystemF.Pat TI] -> SystemF.Pat TI
mkTupleP fs = TITupleP fs

mkVarE :: SourcePos -> SystemF.Var -> TIExp
mkVarE pos v = TIExp $ SystemF.VarE (synInfo pos) v

mkConE :: SourcePos -> SystemF.Var -> TIExp
mkConE pos c = TIExp $ SystemF.VarE (synInfo pos) c

mkLitE :: SourcePos -> SystemF.Lit -> TIType -> TIExp
mkLitE pos l t = TIExp $ SystemF.LitE (synInfo pos) l t

mkTyAppE :: SourcePos -> TIExp -> TIType -> TIExp
mkTyAppE pos oper arg = TIExp $ SystemF.TyAppE (synInfo pos) oper arg

mkUndefinedE :: SourcePos -> TIType -> TIExp
mkUndefinedE pos ty =
  let con = mkConE pos (SystemF.pyonBuiltin SystemF.the_fun_undefined)
  in mkPolyCallE pos con [ty] []

mkIfE :: SourcePos -> TIExp -> TIExp -> TIExp -> TIExp
mkIfE pos cond tr fa =
  let true_alt = TIAlt $
        SystemF.Alt { SystemF.altConstructor =
                         SystemF.pyonBuiltin SystemF.the_True
                    , SystemF.altTyArgs = []
                    , SystemF.altParams = []
                    , SystemF.altBody = tr
                    }
      false_alt = TIAlt $
        SystemF.Alt { SystemF.altConstructor =
                         SystemF.pyonBuiltin SystemF.the_False
                    , SystemF.altTyArgs = []
                    , SystemF.altParams = []
                    , SystemF.altBody = fa
                    }
  in TIExp $ SystemF.CaseE (synInfo pos) cond [true_alt, false_alt]

mkCallE :: SourcePos -> TIExp -> [TIExp] -> TIExp
mkCallE pos oper args = TIExp $ SystemF.CallE (synInfo pos) oper args

-- | Create a call of a polymorphic function with no constraint arguments.
-- This does not follow the calling convention for constraint arguments, which
-- should be \"called\" separately.
mkPolyCallE :: SourcePos -> TIExp -> [TIType] -> [TIExp] -> TIExp
mkPolyCallE pos oper ty_args args =
  let mono_oper = foldl (mkTyAppE pos) oper ty_args
  in if null args
     then mono_oper
     else TIExp $ SystemF.CallE (synInfo pos) mono_oper args

mkLetE :: SourcePos -> SystemF.Pat TI -> TIExp -> TIExp -> TIExp
mkLetE pos lhs rhs body = TIExp $ SystemF.LetE (synInfo pos) lhs rhs body 

mkFunE :: SourcePos -> SystemF.Fun TI -> TIExp
mkFunE pos fun = TIExp $ SystemF.FunE (synInfo pos) fun

mkLetrecE :: SourcePos -> [SystemF.Def TI] -> TIExp -> TIExp
mkLetrecE pos defs body = TIExp $ SystemF.LetrecE (synInfo pos) defs body

mkDictE :: SourcePos -> Class -> TIType -> [TIExp] -> [TIExp] -> TIExp
mkDictE pos cls inst_type scs methods =
  let -- First, apply the dictionary constructor to the instance type
      dict1 = mkTyAppE pos (mkConE pos $ clsDictCon cls) inst_type
      -- Then apply to all arguments
  in mkCallE pos dict1 (scs ++ methods)

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
  let num_superclasses = length $ clsConstraint cls
      num_methods = length $ clsMethods cls
      
  -- Get the type of each field.  Rename the class variable to match
  -- this instance.
  let instantiation = substitutionFromList [(clsParam cls, inst_type)]
  sc_types <- mapM (return . convertPredicate <=< rename instantiation) $
              clsConstraint cls
  m_types <- mapM (return . convertTyScheme <=< renameTyScheme instantiation . clmSignature) $ clsMethods cls

  -- Create anonymous parameter variables
  parameter_vars <- replicateM (num_superclasses + num_methods) $ do
    var_id <- withTheNewVarIdentSupply supplyValue
    return $ mkAnonymousVar var_id ObjectLevel

  -- Create binders for the parameters
  let mkParameter var ty = TIVarP var ty
      parameters = zipWith mkParameter parameter_vars (sc_types ++ m_types)

  -- Create a case expression that matches against the class dictionary,
  -- selects one of its fields, and instantiates the field to a monomorphic
  -- type
  let method_var = mkVarE pos $ parameter_vars !! (num_superclasses + index)
  (placeholders, alt_body) <-
    instanceExpression pos ty_params constraint method_var
      
  let alt = TIAlt $
            SystemF.Alt (clsDictCon cls) [convertHMType inst_type] parameters alt_body

  return (placeholders, TIExp $ SystemF.CaseE (synInfo pos) dict [alt])

-- | Create a placeholder for a recursive variable.  The variable is assumed
-- to have a monomorphic type, which is later generalized.
mkRecVarPlaceholder :: SourcePos
                    -> Untyped.Variable -- ^ The variable
                    -> TyCon    -- ^ Its type (a flexible type variable)
                    -> IO TIExp -- ^ Returns the created placeholder
mkRecVarPlaceholder pos variable ty = do
  tyvar <- newTyVar Star Nothing
  actual <- newEmptyMVar
  return $ RecVarPH (mkSynInfo pos ObjectLevel) variable tyvar actual

mkDictPlaceholder :: SourcePos -> Predicate -> IO TIExp
mkDictPlaceholder pos p = do
  -- Debugging message
  when debugPlaceholders $ do
    ph_doc <- runPpr $ uShow p
    print $ text "Creating placeholder for" <+> ph_doc
  actual <- newEmptyMVar
  return $ DictPH (mkSynInfo pos ObjectLevel) p actual

mkFunction :: SourcePos -> [TyCon] -> [SystemF.Pat TI] -> TIType -> TIExp 
           -> IO (SystemF.Fun TI)
mkFunction pos ty_params params ret_type body = do
  ty_params' <- mapM convertTyParam ty_params
  return $ TIFun $ SystemF.Fun (mkSynInfo pos ObjectLevel) ty_params' params ret_type body
  where
    convertTyParam ty_param = do
      v <- tyVarToSystemF ty_param
      let k = convertKind $ tyConKind ty_param
      return $ SystemF.TyPat v k

mkExport :: SourcePos -> ExportSpec -> SystemF.Fun TI -> SystemF.Export TI
mkExport pos spec f = SystemF.Export pos spec f

-------------------------------------------------------------------------------
-- Conversion to System F

convertKind :: Kind -> TIType
convertKind k = delayType $ SystemF.SFType $ convertKind' k
    
convertKind' Star = Type.Type.pureT
convertKind' (k1 :-> k2) = mkArrowType (convertKind' k1) (convertKind' k2)

convertHMType :: HMType -> TIType
convertHMType ty = DelayedType $ fmap SystemF.SFType $ convertHMType' ty 
                   
convertHMType' ty = do
  ty' <- canonicalizeHead ty
  case ty' of
    ConTy c | isTyVar c -> do
      v <- tyVarToSystemF c
      return $ Type.Type.VarT v
            | otherwise -> do
      sf_ty <- tyConToSystemF c
      return (SystemF.fromSFType sf_ty)
      
    -- Function types should only appear within an AppTy term
    FunTy _ -> fail "Unexpected function type constructor"

    TupleTy n ->
      return $ Type.Type.VarT $ SystemF.pyonTupleTypeCon n

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

mkArrowType :: Type.Type.Type -> Type.Type.Type -> Type.Type.Type
mkArrowType d r = Type.Type.FunT (Type.Type.ValPT Nothing Type.Type.::: d) (Type.Type.ValRT Type.Type.::: r)

-- | Make the type of an uncurried Pyon function from @domain@ to @range@.
--
-- Depending on the calling convention indicated by the range, a stream 
-- function or action function is generated.
mkFunctionType :: [Type.Type.Type]      -- ^ domain
               -> Type.Type.Type        -- ^ range
               -> Type.Type.Type        -- ^ System F type
mkFunctionType domain range =
  foldr mkArrowType range domain

convertPredicate :: Predicate -> TIType
convertPredicate prd = DelayedType $ fmap SystemF.SFType $ convertPredicate' prd 

convertPredicate' (IsInst ty cls) = do
  ty' <- convertHMType' ty
  return $ Type.Type.varApp (clsTypeCon cls) [ty']

-- | Convert a type scheme to a function type.  Each quantified variable
-- becomes a parameter in the function type.
convertTyScheme :: TyScheme -> TIType
convertTyScheme (TyScheme qvars cst ty) = DelayedType $ do
  qvars' <- mapM tyVarToSystemF qvars
  cst' <- mapM convertPredicate' cst
  ty' <- convertHMType' ty
  let constrained_type = mkFunctionType cst' ty'
      parametric_type = foldr mkFun constrained_type (zip qvars qvars')
  return $ SystemF.SFType parametric_type
  where
    mkFun (v, gluon_v) ty =
      let param = Type.Type.ValPT (Just gluon_v) Type.Type.::: convertKind' (tyConKind v)
          result = Type.Type.ValRT Type.Type.::: ty
      in Type.Type.FunT param result

-- | Create an instance expression with placeholders for all constraints
instanceExpression :: SourcePos
                   -> [HMType]   -- ^ Instantiated type parameters
                   -> Constraint -- ^ Instantiated constraint
                   -> TIExp      -- ^ Instantiated first-order expression
                   -> IO (Placeholders, TIExp) 
                      -- ^ Dictionary placeholders and instance expression
instanceExpression pos ty_params constraint exp = do
  -- Apply the instantiated expression to each type parameter
  -- The first type parameter in the list is applied first
  let applyTypeParam exp tp = mkTyAppE pos exp (convertHMType tp)
  let value_exp = foldl applyTypeParam exp ty_params
  
  if null constraint && null ty_params then return ([], value_exp) else do
    -- Create a call expression with placeholder arguments
    placeholders <- mapM (mkDictPlaceholder pos) constraint
    return (placeholders, mkCallE pos value_exp placeholders)

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
  -- Apply the instantiated expression to each type parameter
  -- The first type parameter in the list is applied first
  let applyTypeParam exp tp = mkTyAppE pos exp (convertHMType tp)
  let value_exp = foldl applyTypeParam exp ty_params
  
  if null constraint && null ty_params then return value_exp else do
    -- Create a call expression with class dictionary arguments
    dictionaries <- mapM getProof constraint
    return $ mkCallE pos value_exp dictionaries
  where
    getProof prd = do
      mprf <- lookupProof prd env
      case mprf of
        Just prf -> return prf
        Nothing -> internalError "Cannot find class dictionary"
      