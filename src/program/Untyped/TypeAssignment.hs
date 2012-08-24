
module Untyped.TypeAssignment
       (TypeAssignment,
        pprTypeAssignment,
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
assignedFreeVariables (FirstOrderAssignment ty _) =
  freeTypeVariables ty

assignedFreeVariables (PolymorphicAssignment ty _) =
  freeTypeVariables ty

assignedFreeVariables (DataConAssignment ty _) =
  freeTypeVariables ty
  
assignedFreeVariables (RecursiveAssignment _ tyvar) =
  freeTypeVariables (ConTy tyvar)

assignedFreeVariables (MethodAssignment cls _ ty) =  do
  ftvs <- freeTypeVariables ty
  return $ Set.insert (clsParam $ clsSignature cls) ftvs

typeAssignmentScheme :: TypeAssignment -> TyScheme
typeAssignmentScheme (FirstOrderAssignment ty _) = monomorphic ty
typeAssignmentScheme (PolymorphicAssignment scm _) = scm
typeAssignmentScheme (DataConAssignment scm _) = scm
typeAssignmentScheme (RecursiveAssignment _ _) =
  internalError "Can't get type scheme of recursive variable" 
typeAssignmentScheme (MethodAssignment cls index scm) =
  case scm
  of TyScheme scm_params scm_cst scm_fot ->
       let cls_param = clsParam $ clsSignature cls
           params = cls_param : scm_params
           cst = ConTy cls_param `IsInst` cls : scm_cst
       in TyScheme params cst scm_fot

instantiateTypeAssignment :: SourcePos
                          -> TypeAssignment
                          -> IO (Placeholders, TyVarSet, Constraint, HMType, TIExp)
instantiateTypeAssignment pos ass = 
  case ass
  of FirstOrderAssignment ty mk_exp -> do
       free_vars <- unifiableTypeVariables ty
       return ([], free_vars, [], ty, mk_exp pos)
       
     PolymorphicAssignment ty mk_exp -> do
       (ty_vars, constraint, fot) <- instantiate ty
       (placeholders, exp) <-
         instanceExpression pos (map ConTy ty_vars) constraint (mk_exp pos)
       free_vars <- unifiableTypeVariables fot
       return (placeholders, free_vars, constraint, fot, exp)

     DataConAssignment ty con -> do
       (ty_vars, constraint, fot) <- instantiate ty
       (placeholders, exp) <-
         conInstanceExpression pos (map ConTy ty_vars) constraint con fot
       free_vars <- unifiableTypeVariables fot
       return (placeholders, free_vars, constraint, fot, exp)

     RecursiveAssignment var tyvar -> do
       -- Create a placeholder expression
       let ty = ConTy tyvar
       placeholder <- mkRecVarPlaceholder pos var tyvar
       free_vars <- unifiableTypeVariables ty
       return ([placeholder], free_vars, [], ty, placeholder)

     MethodAssignment cls index scm -> do
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

firstOrderAssignment = FirstOrderAssignment

polymorphicAssignment = PolymorphicAssignment

constructorAssignment = DataConAssignment

-- | Create a type assignment for a recursively defined variable.  The variable
-- is assumed to have an unknown monotype represented by a new type variable.
-- A placeholder expression is inserted wherever the variable is used.
recursiveAssignment :: Variable -> IO (TypeAssignment, TyCon)
recursiveAssignment var = do
  -- Create a new type variable representing the variable's unknown type
  tyvar <- newTyVar Star Nothing
  return (RecursiveAssignment var tyvar, tyvar)

-- | Create a class method assignment.  A class method is really a piece of
--   code that retrieves and calls a function from the class dictionary.
--
--   The class method's type scheme is made from the method's type signature.
--   It has one extra type parameter, which is the class's type parameter, 
--   and one extra predicate, which is the class instance.  The parameter and
--   predicate always come before other parameters and predicates.
methodAssignment = MethodAssignment

pprTypeAssignment :: TypeAssignment -> Ppr Doc
pprTypeAssignment (FirstOrderAssignment ty _) = do
  doc <- uShow ty
  return $ text "(monotype)" <+> doc
  
pprTypeAssignment (PolymorphicAssignment ty _) = do
  doc <- pprTyScheme ty
  return $ text "(polytype)" <+> doc

pprTypeAssignment (DataConAssignment ty _) = do
  doc <- pprTyScheme ty
  return $ text "(datacon)" <+> doc

pprTypeAssignment (RecursiveAssignment v ty) = do
  doc <- uShow (ConTy ty)
  return $ text "(rectype)" <+> doc

pprTypeAssignment (MethodAssignment _ _ ty) = do
  doc <- pprTyScheme ty
  return $ text "(method)" <+> doc
