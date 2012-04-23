{-| This module translates core type declarations in AST form to
--  specification types.  It's used during initialization.
-}

{-# LANGUAGE ViewPatterns #-}
module CParser2.GenCore (createCoreTable) where

import qualified Data.IntMap as IntMap
import Data.List
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.SourcePos
import Common.Error
import Common.Identifier
import Builtins.Builtins
import CParser2.AST
import Type.Type(Binder(..), Level(..))
import qualified Type.Type as Type
import Type.Environment
import qualified Type.Eval as Type
import Type.Var

-- | Verify that the module contains no function definitions.
--   This function throws an error if the check fails.  Its result should
--   be evaluated strictly.
checkModule :: Module Resolved -> Module Resolved
checkModule mod@(Module decls)
  | any is_fun_decl decls =
      internalError "Unexpected function declaration"
  | otherwise = mod
  where
    is_fun_decl ldecl =
      case unLoc ldecl
      of Decl _ (FunEnt _ _) -> True
         _                   -> False

-- | Extract information from an attribute list on a variable declaration
fromVarAttrs :: [Attribute] -> Bool
fromVarAttrs attrs =
  -- Start with default attributes and modify given each attribute
  foldl' interpret False attrs
  where
    interpret st ConlikeAttr = True
    interpret st _ =
      error "Unexpected attribute on type declaration"
  
-------------------------------------------------------------------------------

insertDomain :: Type.Binder -> SpecTypeEnv -> SpecTypeEnv
insertDomain (v ::: t) e = insertType v t e

toVar (ResolvedVar v _) = v

translateDomain :: SpecTypeEnv -> Domain Resolved -> Type.Binder
translateDomain tenv (Domain param ty) = toVar param ::: translateType tenv ty

translateType :: SpecTypeEnv -> RLType -> Type.Type
translateType tenv lty =
  case unLoc lty
  of VarT v -> Type.VarT (toVar v)
     IntIndexT n -> Type.IntT n
     TupleT ts ->
       -- Get kinds of type arguments
       let tys = map (translateType tenv) ts
           kinds = map (Type.toBaseKind . Type.typeKind tenv) tys
       in Type.typeApp (Type.UTupleT kinds) tys

     AppT op arg ->
       Type.AppT (translateType tenv op) (translateType tenv arg)
     FunT dom rng ->
       Type.FunT (translateType tenv dom) (translateType tenv rng)
     AllT (Domain param ty) rng ->
       let dom' = toVar param ::: translateType tenv ty
           rng' = translateType (insertDomain dom' tenv) rng
       in Type.AllT dom' rng'
     LamT doms body ->
       let mk_lambda tenv (Domain param d : ds) body =
             let dom' = toVar param ::: translateType tenv d
                 rng = mk_lambda (insertDomain dom' tenv) ds body
             in Type.LamT dom' rng
           mk_lambda tenv [] body =
             translateType tenv body
       in mk_lambda tenv doms body
     CoT kind dom rng ->
       Type.typeApp (Type.CoT (translateType tenv kind)) 
       [translateType tenv dom, translateType tenv rng]

-- | Translate a data constructor field to the type used for passing the 
--   field as an argument to a constructor application.
translateDataConFieldArgument :: SpecTypeEnv -> RLType -> Type.Type
translateDataConFieldArgument tenv lty =
  let translated_type = translateType tenv lty
      translated_kind = Type.typeKind tenv translated_type
  in case translated_kind
     of Type.VarT kvar
          | kvar == Type.bareV ->
              -- Convert to writer
              Type.varApp (pyonBuiltin The_Init) [translated_type]
          | otherwise -> translated_type

        -- Other terms should not occur 
        _ -> internalError "translateDataConFieldArgument: Unexpected kind"

translateDataConDecl tenv data_type_con decl =
  let params = map (translateDomain tenv) $ dconParams decl
      ex_types = map (translateDomain tenv) $ dconExTypes decl
      local_tenv = foldr insertDomain tenv (params ++ ex_types)
      args = map (translateType local_tenv) $ dconArgs decl
      ty = make_datacon_type params ex_types (dconArgs decl) (range_type params)
  in (ty, DataConType params ex_types args (toVar $ dconVar decl) data_type_con)
  where
    -- Get the type of a fully applied data constructor.
    -- Create a writer type if appropriate.
    range_type params =
      let param_types = [Type.VarT v | v ::: _ <- params]
          range_type = foldl Type.AppT (Type.VarT data_type_con) param_types
          range_kind = Type.typeKind tenv range_type
      in case range_kind
         of Type.VarT kvar
              | kvar == Type.bareV ->
                  -- Convert to writer
                  Type.varApp (pyonBuiltin The_Init) [range_type]
              | otherwise -> range_type

            -- Other terms should not occur 
            _ -> internalError "translateDataConDecl: Unexpected kind"

    -- Create the type of a data constructor, given the types used when
    -- pattern matching on the data constructor
    make_datacon_type params ex_types args rng =
      let ty_params = params ++ ex_types
          local_tenv = foldr insert_type tenv ty_params
            where insert_type (v ::: t) e = insertType v t e
          fields = map (translateDataConFieldArgument local_tenv) args
      in Type.forallType ty_params $ Type.funType fields rng

-- | Translate a global declaration.  The completed type environment may be
--   used lazily in the translation.
translateDecl :: SpecTypeEnv -> Decl Resolved -> (SpecTypeEnv -> SpecTypeEnv)
translateDecl tenv (Decl name ent) =
  case ent
  of VarEnt ty attrs ->
       let conlike = fromVarAttrs attrs
       in conlike `seq`
          insertTypeWithProperties core_name (translateType tenv ty) conlike
     TypeEnt ty (Just type_function) ->
       insertTypeFunction core_name (translateType tenv ty) type_function
     TypeEnt ty Nothing ->
       insertType core_name (translateType tenv ty)
     DataEnt ty data_cons attrs ->
       let kind = translateType tenv ty
           abstract = AbstractAttr `elem` attrs
           algebraic = not $ NonalgebraicAttr `elem` attrs
           data_con_descrs =
             map (translateDataConDecl tenv core_name . unLoc) data_cons
           descr = DataTypeDescr core_name kind data_con_descrs abstract algebraic
       in insertDataType descr
  where
    core_name = toVar name

-- | Create a type environment from the given module AST
createCoreTable mod =
  case checkModule mod
  of Module decls ->
       let tenv = foldr ($) wiredInTypeEnv $ map translate decls
           translate ldecl = translateDecl tenv (unLoc ldecl)
       in tenv

