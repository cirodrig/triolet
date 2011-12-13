
module Untyped.TypeAssignment
       (TypeAssignment,
        assignedFreeVariables,
        instantiateTypeAssignment,
        firstOrderAssignment,
        polymorphicAssignment,
        constructorAssignment,
        recursiveAssignment,
        methodAssignment)
where

import Control.Monad
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.SourcePos
import Untyped.GenSystemF
import Untyped.HMType
import Untyped.Kind
import Untyped.Syntax
import Untyped.Data
import Untyped.Unification
import Type.Var

assignedFreeVariables :: TypeAssignment -> IO TyVarSet
assignedFreeVariables = _typeAssignmentFreeVariables

instantiateTypeAssignment :: SourcePos
                          -> TypeAssignment
                          -> IO (Placeholders, TyVarSet, Constraint, HMType, TIExp)
instantiateTypeAssignment pos ass = _instantiateTypeAssignment ass pos

firstOrderAssignment :: HMType  -- ^ First-order type
                     -> (SourcePos -> TIExp) 
                        -- ^ Factory for an expression of this type 
                     -> TypeAssignment
firstOrderAssignment ty value =
  TypeAssignment (freeTypeVariables ty) (monomorphic ty) instantiate_function
  where
    instantiate_function pos = do
      free_vars <- unifiableTypeVariables ty
      return ([], free_vars, [], ty, value pos)

polymorphicAssignment :: TyScheme -- ^ Polymorphic type
                      -> (SourcePos -> TIExp) 
                         -- ^ Factory for an expression of this type
                      -> TypeAssignment
polymorphicAssignment ty mk_value =
  TypeAssignment (freeTypeVariables ty) ty instantiate_function
  where
    instantiate_function pos = do
      (ty_vars, constraint, fot) <- instantiate ty
      (placeholders, exp) <-
        instanceExpression pos (map ConTy ty_vars) constraint (mk_value pos)
      free_vars <- unifiableTypeVariables fot
      return (placeholders, free_vars, constraint, fot, exp)

constructorAssignment :: TyScheme -- ^ Polymorphic type
                      -> Var      -- ^ Data constructor
                      -> TypeAssignment
constructorAssignment ty con =
  TypeAssignment (freeTypeVariables ty) ty instantiate_con
  where
    instantiate_con pos = do
      (ty_vars, constraint, fot) <- instantiate ty
      (placeholders, exp) <-
        conInstanceExpression pos (map ConTy ty_vars) constraint con fot
      free_vars <- unifiableTypeVariables fot
      return (placeholders, free_vars, constraint, fot, exp)

-- | Create a type assignment for a recursively defined variable.  The variable
-- is assumed to have an unknown monotype represented by a new type variable.
-- A placeholder expression is inserted wherever the variable is used.
recursiveAssignment :: Variable -- ^ Recursively defined variable
                    -> IO (TypeAssignment, TyCon)
recursiveAssignment var = do
  -- Create a new type variable representing the variable's unknown type
  tyvar <- newTyVar Star Nothing
  
  let ty = ConTy tyvar
  let instantiate_function pos = do
        -- Create a placeholder expression
        placeholder <- mkRecVarPlaceholder pos var tyvar
        free_vars <- unifiableTypeVariables ty
        return ([placeholder], free_vars, [], ty, placeholder)

      scheme = internalError "Cannot get type scheme of recursive variable"
  return ( TypeAssignment (freeTypeVariables ty) scheme instantiate_function
         , tyvar)

-- | Create a class method assignment.  A class method is really a piece of
--   code that retrieves and calls a function from the class dictionary.
--
--   The class method's type scheme is made from the method's type signature.
--   It has one extra type parameter, which is the class's type parameter, 
--   and one extra predicate, which is the class instance.  The parameter and
--   predicate always come before other parameters and predicates.
methodAssignment :: Class -> Int -> TyScheme -> TypeAssignment
methodAssignment cls index scm =
  let get_free_variables = do
        ftvs <- freeTypeVariables scm
        return $ Set.insert cls_param ftvs
  in TypeAssignment get_free_variables visible_method_scheme instantiate_function
  where
    cls_param = clsParam $ clsSignature cls

    -- Add the class parameter and the class constraint to the method's scheme.
    -- This is equivalent to the method's type, but doesn't let us keep
    -- track of which parts come from the class versus the method.
    visible_method_scheme =
      case scm
      of TyScheme scm_params scm_cst scm_fot ->
           let params = cls_param : scm_params
               cst = ConTy cls_param `IsInst` cls : scm_cst
           in TyScheme params cst scm_fot

    instantiate_function pos = do
      -- Instantiate the method's type
      (inst_var, cls_cst, cls_prd, inst_vars, inst_cst, fot) <-
        instantiateClassMethod cls scm
      free_vars <- unifiableTypeVariables fot

      -- Remove the class parameter from the type
      let cls_type = case cls_prd of ty `IsInst` _ -> ty

      -- Create a placeholder for the class dictionary
      cls_placeholder <- mkDictPlaceholder pos cls_prd

      -- Create a method selector expression and instantiate the method
      (inst_placeholders, expr) <-
        mkMethodInstanceE pos cls cls_type index (map ConTy inst_vars) inst_cst cls_placeholder

      let placeholders = cls_placeholder : inst_placeholders
          constraint = cls_prd : cls_cst ++ inst_cst

      -- DEBUG: print out the results of instantiating the class method
      -- printMethodAssignmentResult placeholders free_vars constraint fot
      return (placeholders, free_vars, constraint, fot, expr)

printMethodAssignmentResult placeholders free_vars constraint fot = do
  (ph_doc, fv_doc, cst_doc, fot_doc) <- runPpr $ do
    ph_docs <- forM placeholders $ \(DictPH {phExpPredicate = pred}) -> do
      uShow pred

    fv_doc <- mapM pprTyCon $ Set.toList free_vars
    cst_doc <- mapM uShow constraint
    fot_doc <- uShow fot
    return (vcat ph_docs, fv_doc, fsep $ punctuate (text ",") cst_doc, fot_doc)

  print "Instantiated method assignment"
  print ph_doc
  print fv_doc
  print cst_doc
  print fot_doc
