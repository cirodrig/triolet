{- | Helper routines to convert from untyped code to System F code.
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
module Pyon.Untyped.GenSystemF where

import Prelude hiding(mapM)
import Control.Applicative
import Control.Concurrent.MVar
import Control.Monad hiding(forM, mapM)
import Data.Function
import qualified Data.Set as Set
import Data.Traversable
import Data.Typeable(Typeable)
import qualified Data.Map as Map
import Text.PrettyPrint.HughesPJ(text, (<+>), parens)

import Gluon.Common.Error
import Gluon.Common.MonadLogic
import Gluon.Common.SourcePos
import Gluon.Core.Level
import Gluon.Core.Builtins
import Gluon.Core(SynInfo, mkSynInfo, internalSynInfo,
                  Structure, Rec, ExpOf(..))
import qualified Gluon.Core as Gluon
import Pyon.Globals
import Pyon.Untyped.Kind
import Pyon.Untyped.HMType
import qualified Pyon.Untyped.Syntax as Untyped
import qualified Pyon.SystemF.Syntax as SystemF
import qualified Pyon.SystemF.Builtins as SystemF

debugPlaceholders = False

-------------------------------------------------------------------------------
-- Type schemes

-- | A type scheme
data TyScheme = TyScheme TyVars Constraint HMType

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
  qvars <- forM kinds $ \k -> newTyVar k () Nothing
  
  -- This must be lazy, because it's used when creating classes and the
  -- constraint may refer to a class
  return $ case f qvars
           of (cst, ty) -> TyScheme qvars cst ty

-- | Instantiate a type scheme by giving fresh names to all type variables
instantiate :: TyScheme -> IO (TyVars, Constraint, HMType)
instantiate (TyScheme qvars cst ty) = do
  -- Create a substitution from each qvar to a new variable 
  new_qvars <- mapM duplicateTyVar qvars
  let substitution = Map.fromList $ zip qvars $ map ConTy new_qvars

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

-------------------------------------------------------------------------------
-- Type classes

-- | A type class.
--
-- The type class's name is used as a globally unique identifier.
--
-- The class's method and instance lists must be non-strict.  Methods and 
-- instances contain references back to the parent class.
data Class =
  Class
  { clsParam :: TyCon
  , clsConstraint :: Constraint
  , clsMethods :: [ClassMethod]
  , clsName :: String
  , clsInstances :: [Instance]
  , clsTypeCon :: !Gluon.Con    -- ^ Class dictionary type constructor
  , clsDictCon :: !Gluon.Con    -- ^ Class dictionary constructor
  }

instance Eq Class where
  (==) = (==) `on` clsName

-- | A class method interface declaration.  Information used for class
-- type and constraint inference is here.  The method's implementation is in
-- the instance method.
data ClassMethod =
  ClassMethod
  { clmName :: String
    -- | The type signature of a method retrieved from the class dictionary.  
    -- The class's parameter variables and the class constraint itself are not
    -- part of the signature.
  , clmSignature :: TyScheme
    -- | The variable that represents this method in source code 
  , clmVariable :: Untyped.Variable
  }

-- | A class instance
data Instance =
  Instance
  { insQVars :: TyVars
  , insConstraint :: Constraint
  , insClass :: Class
  , insType :: HMType
  , insMethods :: [InstanceMethod]
  }

-- | Each instance method is defined as some constructor in System F
newtype InstanceMethod = InstanceMethod {inmName :: Gluon.Con}

-- | Construct a type scheme representing all types covered by this instance
insScheme :: Instance -> TyScheme
insScheme i = TyScheme (insQVars i) (insConstraint i) (insType i)

-- | A predicate to be solved by type inference
data Predicate =
  -- | The type is an instance of the class
  IsInst HMType !Class

type Constraint = [Predicate]

instance Type Predicate where
  freeTypeVariables (IsInst t _) = freeTypeVariables t

instance Type [Predicate] where
  freeTypeVariables xs = liftM Set.unions $ mapM freeTypeVariables xs

instance Unifiable Predicate where
  uShow xs = runTypeDisplayer $ traverse showPredicate xs
    where
      showPredicate (t `IsInst` c) = display <$> displayType t
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

-- | A derivation of a predicate, containing enough information to reconstruct
-- the derivation steps in the form of a proof object
data Derivation =
    -- | A trivial derivation using an already-existing proof 
    IdDerivation 
    { conclusion :: Predicate
    }
    -- | A derivation using a class instance
  | InstanceDerivation 
    { conclusion :: Predicate 
    , derivedInstance :: Instance
    , instancePremises :: [Derivation] 
    , classPremises :: [Derivation]
    }

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

-------------------------------------------------------------------------------
-- Type inference System F data structures

-- | Internal type inference representation of System F
data TI deriving(Typeable)
instance Structure TI

-- | Type inferred expressions, which may contain placeholders
data instance SystemF.SFExpOf TI TI =
    -- | A placeholder for a recursive variable
    RecVarPH
    { phExpInfo :: SynInfo
    , phExpVariable :: Untyped.Variable
    , phExpTyVar :: TyCon
    , phExpResolution :: {-# UNPACK #-} !(MVar TIExp)
    }
    -- | A placeholder for a class dictionary
  | DictPH
    { phExpInfo :: SynInfo
    , phExpPredicate :: Predicate
    , phExpResolution :: {-# UNPACK #-} !(MVar TIExp)
    }
    -- | A non-placeholder expression
  | TIExp !TIExp'
    
    -- | An expression that was written directly in System F
    --
    -- This kind of expression only comes from built-in terms.
  | TIRecExp SystemF.RExp

-- | A type inference System F expression
type TIExp = SystemF.SFExpOf TI TI

-- | Other expressions use regular System F constructors
type TIExp' = SystemF.SFExpOf Rec TI

-- | A Placeholder is a RecVarPH or DictPH term
type Placeholder = TIExp
type Placeholders = [Placeholder]

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

-- | Types are not evaluated until type inference completes
newtype instance ExpOf TI TI = DelayedType (IO Gluon.RExp)

type TIType = SystemF.TypeOf TI TI

delayType :: Gluon.RExp -> TIType
delayType t = DelayedType (return t)

objectSynInfo :: SynInfo
objectSynInfo = internalSynInfo ObjectLevel

synInfo :: SourcePos -> SynInfo
synInfo pos = mkSynInfo pos ObjectLevel

mkWildP :: TIType -> SystemF.Pat TI
mkWildP ty = SystemF.WildP ty

mkVarP :: SystemF.Var -> TIType -> SystemF.Pat TI 
mkVarP v ty = SystemF.VarP v ty

mkTupleP :: [SystemF.Pat TI] -> SystemF.Pat TI
mkTupleP fs = SystemF.TupleP fs

mkVarE :: SourcePos -> SystemF.Var -> TIExp
mkVarE pos v = TIExp $ SystemF.VarE (synInfo pos) v

mkConE :: SourcePos -> Gluon.Con -> TIExp
mkConE pos c = TIExp $ SystemF.ConE (synInfo pos) c

mkLitE :: SourcePos -> SystemF.Lit -> TIType -> TIExp
mkLitE pos l t = TIExp $ SystemF.LitE (synInfo pos) l t

mkTyAppE :: SourcePos -> TIExp -> TIType -> TIExp
mkTyAppE pos oper arg = TIExp $ SystemF.TyAppE (synInfo pos) oper arg

mkUndefinedE :: SourcePos -> TIType -> TIExp
mkUndefinedE pos ty = TIExp $ SystemF.UndefinedE (synInfo pos) ty

mkIfE :: SourcePos -> TIExp -> TIExp -> TIExp -> TIExp
mkIfE pos cond tr fa = TIExp $ SystemF.IfE (synInfo pos) cond tr fa

mkTupleE :: SourcePos -> [TIExp] -> TIExp
mkTupleE pos fields = TIExp $ SystemF.TupleE (synInfo pos) fields

mkCallE :: SourcePos -> TIExp -> [TIExp] -> TIExp
mkCallE pos oper args = TIExp $ SystemF.CallE (synInfo pos) oper args

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

mkMethodSelectE :: SourcePos -> Class -> TIType -> Int -> TIExp -> IO TIExp
mkMethodSelectE pos cls inst_type index dict = do
  let num_superclasses = length $ clsConstraint cls
      num_methods = length $ clsMethods cls
  
  -- Create anonymous parameter variables
  parameter_vars <- replicateM (num_superclasses + num_methods) $ do
    var_id <- getNextVarIdent
    return $ Gluon.mkAnonymousVariable var_id ObjectLevel

  -- Create a case expression that matches against the class dictionary
  -- and then selects one of its fields
  let alt_body = mkVarE pos $ parameter_vars !! (num_superclasses + index)
      alt = SystemF.Alt (clsDictCon cls) [inst_type] parameter_vars alt_body
            
  return $ TIExp $ SystemF.CaseE (synInfo pos) dict [alt]

-- | Create a placeholder for a recursive variable.  The variable is assumed
-- to have a monomorphic type, which is later generalized.
mkRecVarPlaceholder :: SourcePos
                    -> Untyped.Variable -- ^ The variable
                    -> TyCon    -- ^ Its type (a flexible type variable)
                    -> IO TIExp -- ^ Returns the created placeholder
mkRecVarPlaceholder pos variable ty = do
  tyvar <- newTyVar Star () Nothing
  actual <- newEmptyMVar
  return $ RecVarPH (mkSynInfo pos ObjectLevel) variable tyvar actual

mkDictPlaceholder :: SourcePos -> Predicate -> IO TIExp
mkDictPlaceholder pos p = do
  -- Debugging message
  when debugPlaceholders $ do
    [ph_doc] <- uShow [p]
    print $ text "Creating placeholder for" <+> ph_doc
  actual <- newEmptyMVar
  return $ DictPH (mkSynInfo pos ObjectLevel) p actual

mkFunction :: [TyCon] -> [SystemF.Pat TI] -> TIType -> TIExp 
           -> IO (SystemF.Fun TI)
mkFunction ty_params params ret_type body = do
  ty_params' <- mapM convertTyParam ty_params
  return $ SystemF.Fun ty_params' params ret_type body
  where
    convertTyParam ty_param = do
      v <- tyVarToSystemF ty_param
      let k = convertKind $ tyConKind ty_param
      return $ SystemF.TyPat v k

-------------------------------------------------------------------------------
-- Conversion to System F

convertKind :: Kind -> TIType
convertKind k = delayType $ convertKind' k
    
convertKind' Star =
  Gluon.pureKindE

convertKind' (k1 :-> k2) =
  Gluon.mkArrowE noSourcePos False (convertKind' k1) (convertKind' k2)

convertHMType :: HMType -> TIType
convertHMType ty = DelayedType $ convertHMType' ty 
                   
convertHMType' ty = do
  ty' <- canonicalizeHead ty
  case ty' of
    ConTy c | isTyVar c -> do
      v <- tyVarToSystemF c
      return $ VarE (internalSynInfo TypeLevel) v
            | otherwise ->
      tyConToSystemF c
      
    -- Function types should only appear within an AppTy term
    FunTy _ -> fail "Unexpected function type constructor"

    TupleTy n ->
      return $ ConE (internalSynInfo TypeLevel) $ SystemF.getPyonTupleType' n

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
          return $ Gluon.mkAppE noSourcePos oper_type arg_types
                   
-- | Make the type of an uncurried Pyon function from @domain@ to @range@.
--
-- Depending on the calling convention indicated by the range, a stream 
-- function or action function is generated.
mkFunctionType :: [SystemF.RType]      -- ^ domain
               -> SystemF.RType        -- ^ range
               -> SystemF.RType        -- ^ System F type
mkFunctionType domain range =
  foldr (Gluon.mkArrowE noSourcePos False) range domain

convertPredicate :: Predicate -> TIType
convertPredicate prd = DelayedType $ convertPredicate' prd 

convertPredicate'(IsInst ty cls) = do
  ty' <- convertHMType' ty
  return $ Gluon.mkConAppE noSourcePos (clsTypeCon cls) [ty']

-- | Convert a type scheme to a function type.  Each quantified variable
-- becomes a parameter in the function type.
convertTyScheme :: TyScheme -> TIType
convertTyScheme (TyScheme qvars cst ty) = DelayedType $ do
  qvars' <- mapM tyVarToSystemF qvars
  cst' <- mapM convertPredicate' cst
  ty' <- convertHMType' ty
  let constrained_type = foldr (Gluon.mkArrowE noSourcePos False) ty' cst'
      parametric_type = foldr mkFun constrained_type (zip qvars qvars')
  return parametric_type
  where
    mkFun (v, gluon_v) ty =
      Gluon.mkFunE noSourcePos False gluon_v (convertKind' $ tyConKind v) ty

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
  
  if null constraint then return ([], value_exp) else do
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
  
  if null constraint then return value_exp else do
    -- Create a call expression with class dictionary arguments
    dictionaries <- mapM getProof constraint
    return $ mkCallE pos value_exp dictionaries
  where
    getProof prd = do
      mprf <- lookupProof prd env
      case mprf of
        Just prf -> return prf
        Nothing -> internalError "Cannot find class dictionary"
      