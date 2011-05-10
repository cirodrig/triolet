
{-# LANGUAGE ViewPatterns #-}
module CParser2.GenCore (createCoreTable) where

import qualified Data.IntMap as IntMap
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.SourcePos
import Common.Error
import Common.Identifier
import Builtins.Builtins
import CParser2.AST
import Type.Type((:::)(..), Level(..))
import qualified Type.Type as Type
import Type.Environment
import qualified Type.Eval as Type
import Type.Var

-------------------------------------------------------------------------------

toVar (ResolvedVar v _) = v

translateDomain :: Domain Resolved -> Type.ParamType
translateDomain (Domain param ty) =
  Type.ValPT (Just $ toVar param) ::: translateType ty

translateParamType :: RLType -> Type.ParamType
translateParamType t = Type.ValPT Nothing ::: translateType t

translateReturn :: RLType -> Type.ReturnType
translateReturn t = Type.ValRT ::: translateType t

translateType :: RLType -> Type.Type
translateType lty =
  case unLoc lty
  of VarT v -> Type.VarT (toVar v)
     IntIndexT n -> Type.IntT n
     AppT op arg ->
       Type.AppT (translateType op) (translateType arg)
     FunT dom rng ->
       Type.FunT (translateParamType dom) (translateReturn rng)
     AllT (Domain param ty) rng ->
       Type.AllT (toVar param) (translateType ty) (translateReturn rng)

-- | Translate a data constructor field to the type used for passing the 
--   field as an argument to a constructor application.
translateDataConFieldArgument :: TypeEnv -> RLType -> Type.ParamType
translateDataConFieldArgument tenv lty =
  let translated_type = translateType lty
      translated_kind = Type.typeKind tenv translated_type
  in case translated_kind
     of Type.VarT kvar
          | kvar == Type.bareV ->
              -- Convert to writer
              Type.ValPT Nothing ::: Type.varApp (pyonBuiltin the_write) [translated_type]
          | otherwise -> Type.ValPT Nothing ::: translated_type

        -- Other terms should not occur 
        _ -> internalError "translateDataConFieldArgument: Unexpected kind"

translateDataConDecl tenv data_type_con decl =
  let params = map translateDomain $ dconParams decl
      ex_types = map translateDomain $ dconExTypes decl
      args = map translateReturn $ dconArgs decl
      rng = translateReturn $ dconRng decl
      ty = make_datacon_type params ex_types (dconArgs decl) (dconRng decl)
  in (ty, DataConType params ex_types args rng (toVar $ dconVar decl) data_type_con)
  where
    -- Create the type of a data constructor, given the types used when
    -- pattern matching on the data constructor
    make_datacon_type params ex_types args rng =
      let ty_params = params ++ ex_types
          fields = map (translateDataConFieldArgument tenv) args
          return = case translateDataConFieldArgument tenv rng
                   of _ ::: t -> Type.ValRT ::: t
      in make_params ty_params $ make_function fields return
    
    make_params :: [Type.ParamType] -> Type.ReturnType -> Type.ReturnType
    make_params binders x = foldr make_param x binders
      where
        make_param (Type.ValPT (Just v) ::: t) t' = Type.ValRT ::: Type.AllT v t t'
    
    make_function :: [Type.ParamType] -> Type.ReturnType -> Type.ReturnType
    make_function domains range = foldr mkfun range domains 
      where
        mkfun dom rng = Type.ValRT ::: (dom `Type.FunT` rng)

-- | Translate a global declaration.  The completed type environment may be
--   used lazily in the translation.
translateDecl :: TypeEnv -> Decl Resolved -> (TypeEnv -> TypeEnv)
translateDecl tenv (Decl name ent) =
  case ent
  of VarEnt ty ->
       insertType core_name (translateReturn ty)
     TypeEnt ty (Just type_function) ->
       insertTypeFunction core_name (translateReturn ty) type_function
     TypeEnt ty Nothing ->
       insertType core_name (translateReturn ty)
     DataEnt ty data_cons ->
       let descr = DataTypeDescr core_name (translateReturn ty) Type.Value
                   (map (translateDataConDecl tenv core_name . unLoc) data_cons)
       in insertDataType descr
  where
    core_name = toVar name

createCoreTable (Module decls) =
  let tenv = foldr ($) wiredInTypeEnv $ map translate decls
      translate ldecl = translateDecl tenv (unLoc ldecl)
  in tenv
