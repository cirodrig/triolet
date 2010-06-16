
module Pyon.Untyped.TypeAssignment
       (TypeAssignment,
        assignedFreeVariables,
        assignedTyScheme,
        instantiateTypeAssignment,
        firstOrderAssignment,
        polymorphicAssignment,
        recursiveAssignment,
        methodAssignment)
where

import Control.Monad

import Gluon.Common.Error
import Gluon.Common.SourcePos
import Pyon.Untyped.GenSystemF
import Pyon.Untyped.HMType
import Pyon.Untyped.Kind
import Pyon.Untyped.Syntax
import Pyon.Untyped.Data

assignedFreeVariables :: TypeAssignment -> IO TyVarSet
assignedFreeVariables = _typeAssignmentFreeVariables

assignedTyScheme :: TypeAssignment -> TyScheme
assignedTyScheme = _typeAssignmentScheme

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

-- | Create a class method assignment
methodAssignment :: Class -> Int -> TyScheme -> TypeAssignment
methodAssignment cls index scm =
  TypeAssignment (freeTypeVariables scm) scm instantiate_function
  where
    instantiate_function pos = do
      (ty_vars, constraint, fot) <- instantiate scm
      free_vars <- unifiableTypeVariables fot

      -- The head of the constraint list is always the class constraint
      case constraint of
        cls_predicate@(IsInst cls_type cls2) : constraint'
          | cls == cls2 -> do
              -- The first type variable is the class variable
              let (cls_var : ty_vars') = ty_vars
          
              -- Create a placeholder for the class dictionary
              placeholder <- mkDictPlaceholder pos cls_predicate
      
              -- Create a method selector expression
              (placeholders, expr) <-
                mkMethodInstanceE pos cls cls_type index (map ConTy ty_vars') constraint' placeholder
              
              return ( placeholder : placeholders 
                     , free_vars
                     , constraint
                     , fot
                     , expr
                     )
        _ -> internalError "Unexpected constraint on class method"
