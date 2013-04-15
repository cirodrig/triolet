
{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}
module Untyped.Instantiation where

import Control.Monad
import qualified Data.Set as Set
import Debug.Trace

import Common.Error
import Common.SourcePos
import Untyped.Builtins2
import Untyped.TIExp
import Untyped.TIExpConstructors
import Untyped.Kind
import Untyped.TIMonad
import Untyped.Type
import Untyped.TypeUnif
import Untyped.Unif
import Untyped.Variable
import qualified Type.Var as SF
import qualified Type.Type as SF

-- | Create a monomorphic lambda function representing a parametric term.
--   If no parameters are given, create the term without any lambda function.
mkLambda :: SourcePos -> [HMType] -> HMType -> ([TIExp] -> TI TIExp)
         -> TI TIExp
mkLambda _ [] _ mk_body = mk_body []

mkLambda pos param_types return_type mk_body = do
  -- Create patterns and arguments
  (patterns, arguments) <- liftM unzip $ forM param_types $ \ty -> do
    v <- SF.newAnonymousVar SF.TypeLevel
    repr <- requireRepr ty
    let pat = TIVarP v (mkType ty)
        exp = VarTE (tiInfo pos repr) v
    return (pat, exp)

  let ti_return_type = mkType return_type
  body <- mk_body arguments
  return $ mkFunE pos $ TIFun pos [] patterns ti_return_type body

-- | Compute the representation of a polymorphic thing, given its instantiated
--   representation.
polyThingRepr :: TIRepr -> [HMType] -> [a] -> TIRepr
polyThingRepr repr inst_types placeholders =
  case repr
  of -- If the instantiated thing is boxed or uncoerced,
     -- so is the original thing
     TIBoxed -> TIBoxed
     TIUncoercedVal -> TIUncoercedVal

     -- If it's monomorphic, it has the same representation.
     TIInferredRepr _ | null inst_types && null placeholders -> repr
     TICoreRepr _ _ _ | null inst_types && null placeholders -> repr

     _ -> internalError "polyThingRepr: Unhandled case"

-- | The type of an instance of a qualified object
data InstanceType a = InstanceType [HMType] Constraint a

-- | An instance of a qualified object.
--
--   This instance contains enough information to actually create the object.
data InstanceValue a = InstanceValue [HMType] [TIExp] TIRepr a

-- | Convert an 'Instance' to a function call
instanceCall :: SourcePos -> InstanceValue TIExp -> TIExp
instanceCall pos (InstanceValue params dicts repr exp) =
  mkAppE pos repr exp (map mkType params) dicts

-- | Instantiate a list of variables.  Also create a substitution from the
--   original to the instantiated variables.
instantiateParams :: [TyCon] -> TI ([HMType], CSubstitution)
instantiateParams params = do
  inst_params <- mapM instantiateTyVar params
  let inst_types = map VarTy inst_params
      subst = listCSubstitution $ zip params inst_types
  return (inst_types, subst)

-- | Instantiate a qualified thing at a new type.
--   New, unifiable type variables are created.
instantiateType :: CTerm a => Qualified a -> TI (InstanceType a)
instantiateType (Qualified params cst x) = do
  (inst_types, subst) <- instantiateParams params
  cst' <- substituteC subst cst
  x' <- substituteC subst x
  return $ InstanceType inst_types cst' x'

-- | Instantiate a polymorphic value to a new type
instantiate :: CTerm a => ([HMType] -> a -> HMType)
            -> Qualified a -> TI (InstanceValue a)
instantiate mk_type scheme = do
  -- Compute instantiated type
  InstanceType inst_types cst x <- instantiateType scheme
  -- Create placeholders
  dicts <- requireConstraint cst

  -- Create representation dictionary
  repr <- requireRepr $ mk_type inst_types x

  return $ InstanceValue inst_types dicts repr x

-------------------------------------------------------------------------------

-- | Attempt to match a qualified thing against a given type.
--   If successful, then instantiate it.
matchInstance :: (NormalizeContext HMType m, CTerm a) =>
                 (a -> HMType)  -- ^ Extract type to unify
              -> Qualified a    -- ^ Polymorphic thing
              -> HMType         -- ^ Type to match against
              -> m (Maybe (InstanceType a))
matchInstance get_type (Qualified params cst range) match_ty = do
  unify_result <- matchC (Set.fromList params) (get_type range) match_ty
  case unify_result of
    Nothing -> return Nothing   -- Unification failed
    Just (subst, match_cst) -> do
      -- Constraint produced by matching must be empty, because type families
      -- are not permitted in instance heads
      unless (null match_cst) $
        internalError "matchInstance: equality constraints generated by match"

      let args = [lookupCSubstitution' p subst | p <- params]
      cst' <- substituteC subst cst
      range' <- substituteC subst range
      return $ Just $ InstanceType args cst' range'

-- | Search for an instance that matches a given type.  Return the
--   instantiated matching instance.
findInstance :: (NormalizeContext HMType m, CTerm a) =>
                Instances a     -- ^ List of instances to search
             -> HMType          -- ^ Type to match against
             -> m (Maybe (InstanceType (Instance a)))
findInstance (inst:insts) ty = do
  m_match <- matchInstance instHead inst ty
  case m_match of
    Nothing -> findInstance insts ty
    Just i  -> return $ Just i

findInstance [] _ = return Nothing

-------------------------------------------------------------------------------
  
instantiateVar :: SourcePos -> Variable -> TI (HMType, TIExp)
instantiateVar pos v = getVarBinding v >>= dispatch 
  where
    dispatch (PolyVarAss scm)    = instantiatePolyVar pos v scm
    dispatch (MonoVarAss ty)     = instantiateMonoVar pos v ty
    dispatch (RecVarAss inf)     = instantiateRecVar pos v (recVarType inf)
                                   (recVarValue inf)
    dispatch (DataConAss dc)     = instantiateDataCon pos v dc
    dispatch (MethodAss cls ix)  = instantiateMethod pos cls ix

getVarType :: Variable -> TI HMType
getVarType v = do
  (t, _) <- instantiateVar noSourcePos v
  return t

-- | Create a new instance of a variable that has a polymorphic type
instantiatePolyVar :: SourcePos -> Variable -> TyScheme -> TI (HMType, TIExp)
instantiatePolyVar pos v scm = do
  InstanceValue inst_types dicts repr ty <- instantiate (\_ t -> t) scm
  let Just sf_var = varSystemFVariable v
      ty_args = map mkType inst_types

  -- Compute the polymorphic variable's representation
  let poly_var_repr = polyThingRepr repr inst_types dicts
      poly_var = mkVarE pos poly_var_repr sf_var
      poly_exp = mkPolyCallE pos repr poly_var ty_args dicts

  return (ty, poly_exp)

-- | Create a new instance of a variable that has a monomorphic type
instantiateMonoVar :: SourcePos -> Variable -> HMType -> TI (HMType, TIExp)
instantiateMonoVar pos v ty = do
  let Just sf_var = varSystemFVariable v
  repr <- requireRepr ty
  return (ty, mkVarE pos repr sf_var)

instantiateRecVar :: SourcePos -> Variable -> TyVar -> RecVarP
                  -> TI (HMType, TIExp)
instantiateRecVar pos v ty_var ph = do
  let Just sf_var = varSystemFVariable v
      ty = VarTy ty_var
  repr <- requireRepr ty
  return (ty, PlaceholderTE $ RecVarPlaceholder ph)

-- | Create a new instance of a data constructor.
--   If the data constructor takes field arguments, a lambda function is
--   created.
instantiateDataCon :: SourcePos -> Variable -> DataCon -> TI (HMType, TIExp)
instantiateDataCon pos v con = do
  -- Instantiate the data constructor
  InstanceType inst_types dict_cst (field_tys, FOConstructor tc) <-
    instantiateType $ dcSignature con

  -- Data type is @tc as@ for constructor 'tc' and types 'as'
  let data_type = ConTy tc `appTys` inst_types
  -- Data type constructor's type is @field_tys -> tc as@
  let constructor_type = field_tys `functionTy` data_type

  -- Generate constraints
  dicts <- requireConstraint dict_cst
  repr <- requireRepr $ ConTy tc `appTys` inst_types

  -- Get the type arguments of all 'Repr' predicates
  let dict_types = map unrepr dict_cst
        where
          -- Only representation predicates may appear on data constructors
          unrepr (IsInst cls t) | cls == builtinTyCon TheTC_Repr = t

  -- Create the data expression or function
  let mk_expr fields =
        let Just sf_con = varSystemFVariable v
            tyob_con = dcTyObjectConstructor con
            sf_types = map mkType inst_types
            sizes = [ TISize (mkType ty) (TIInferredRepr d)
                    | (d, ty) <- zip dicts dict_types]
        in return $ mkConE pos repr sf_con sf_types [] sizes tyob_con fields

  exp <- mkLambda pos field_tys data_type mk_expr
  return (constructor_type, exp)

instantiateMethod :: SourcePos -> TyCon -> Int -> TI (HMType, TIExp)
instantiateMethod pos cls_tycon method_index = do
  -- Instantiate the class signature
  Just cls <- getTyConClass cls_tycon
  InstanceType [inst_type] superclass_cst methods <-
    instantiateType $ clsSignature cls

  -- Deconstruct the class dictionary
  c_dict <- requirePredicate $ IsInst cls_tycon inst_type
  (mk_case, _, method_vars) <-
    mkCaseOfDict pos cls inst_type superclass_cst methods c_dict

  -- Instantiate the method
  let method_var = method_vars !! method_index
      method_scheme = clmSignature $ methods !! method_index

  InstanceValue m_inst_types m_inst_dicts repr ty <-
    instantiate (\_ t -> t) method_scheme

  -- Compute the method's representation
  let inst_method_repr = polyThingRepr repr m_inst_types m_inst_dicts
      inst_var = mkVarE pos inst_method_repr method_var

  -- Create the instance
  let inst_ty_args = map mkType m_inst_types
      inst_exp = mkPolyCallE pos repr inst_var inst_ty_args m_inst_dicts

  return (ty, mk_case inst_exp)

-- | Instantiate a class's signature to the given type
instantiateClass :: NormalizeContext HMType m =>
                    Class -> HMType -> m (InstanceType [ClassMethod])
instantiateClass cls ty = do
  m_result <- matchInstance get_class_type signature ty
  return $! case m_result
            of Just x  -> x
               -- The class type should match anything
               Nothing -> internalError "instantiateClass"
  where
    signature = clsSignature cls

    -- The class type is simply the parameter variable
    get_class_type _ = case qParams signature of [v] -> ConTy v

-- | Instantiate a class's signature to the given type, ignoring the class
--   methods' types.
instantiateClassType :: NormalizeContext HMType m =>
                        Class -> HMType -> m (InstanceType ())
instantiateClassType cls ty = do
  m_result <- matchInstance get_class_type (fmap (const ()) signature) ty
  return $! case m_result
            of Just x  -> x
               -- The class type should match anything
               Nothing -> internalError "instantiateClass"
  where
    signature = clsSignature cls

    -- The class type is simply the parameter variable
    get_class_type _ = case qParams signature of [v] -> ConTy v


-------------------------------------------------------------------------------

-- | Create a new placeholder value standing for a predicate
requirePredicate :: Predicate -> TI TIExp
requirePredicate prd = do
  require [prd]                               -- Add to constraint set
  PlaceholderTE `liftM` mkDictPlaceholder prd -- Add to placeholder set

requireConstraint :: Constraint -> TI [TIExp]
requireConstraint cst = do
  require cst
  mapM (return . PlaceholderTE <=< mkDictPlaceholder) cst

-- | Compute the representation dictionary for a type of kind @Star@.
--   If the type is a function type or boxed data type, then no dictionary
--   is needed.
requireRepr :: HMType -> TI TIRepr
requireRepr ty = do 
  (op, args) <- uncurryApp ty
  case op of
    FunTy _ -> is_boxed
    ConTy c -> do
      m_dtype <- getTyConDataType c
      case m_dtype of
        Just dtype | dtBoxed dtype -> is_boxed
        _ -> not_boxed
    _ -> not_boxed
  where
    is_boxed = return $ TIBoxed
    not_boxed = let inst = IsInst (builtinTyCon TheTC_Repr) ty
                in fmap TIInferredRepr $ requirePredicate inst
