
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
import Type.Type(Binder(..), Level(..))
import qualified Type.Type as Type
import Type.Environment
import qualified Type.Eval as Type
import Type.Var

-------------------------------------------------------------------------------

toVar (ResolvedVar v _) = v

translateDomain :: Domain Resolved -> Type.Binder
translateDomain (Domain param ty) = toVar param ::: translateType ty

translateType :: RLType -> Type.Type
translateType lty =
  case unLoc lty
  of VarT v -> Type.VarT (toVar v)
     IntIndexT n -> Type.IntT n
     AppT op arg ->
       Type.AppT (translateType op) (translateType arg)
     FunT dom rng ->
       Type.FunT (translateType dom) (translateType rng)
     AllT (Domain param ty) rng ->
       Type.AllT (toVar param ::: translateType ty) (translateType rng)

-- | Translate a data constructor field to the type used for passing the 
--   field as an argument to a constructor application.
translateDataConFieldArgument :: TypeEnv -> RLType -> Type.Type
translateDataConFieldArgument tenv lty =
  let translated_type = translateType lty
      translated_kind = Type.typeKind tenv translated_type
  in case translated_kind
     of Type.VarT kvar
          | kvar == Type.bareV ->
              -- Convert to writer
              Type.varApp (pyonBuiltin the_Writer) [translated_type]
          | otherwise -> translated_type

        -- Other terms should not occur 
        _ -> internalError "translateDataConFieldArgument: Unexpected kind"

translateDataConDecl tenv data_type_con decl =
  let params = map translateDomain $ dconParams decl
      ex_types = map translateDomain $ dconExTypes decl
      args = map translateType $ dconArgs decl
      rng = translateType $ dconRng decl
      ty = make_datacon_type params ex_types (dconArgs decl) (dconRng decl)
  in (ty, DataConType params ex_types args rng (toVar $ dconVar decl) data_type_con)
  where
    -- Create the type of a data constructor, given the types used when
    -- pattern matching on the data constructor
    make_datacon_type params ex_types args rng =
      let ty_params = params ++ ex_types
          local_tenv = foldr insert_type tenv ty_params
            where insert_type (v ::: t) e = insertType v t e
          fields = map (translateDataConFieldArgument local_tenv) args
          return = translateDataConFieldArgument local_tenv rng
      in Type.forallType ty_params $ Type.funType fields return

-- | Translate a global declaration.  The completed type environment may be
--   used lazily in the translation.
translateDecl :: TypeEnv -> Decl Resolved -> (TypeEnv -> TypeEnv)
translateDecl tenv (Decl name ent) =
  case ent
  of VarEnt ty ->
       insertType core_name (translateType ty)
     TypeEnt ty (Just type_function) ->
       insertTypeFunction core_name (translateType ty) type_function
     TypeEnt ty Nothing ->
       insertType core_name (translateType ty)
     DataEnt ty data_cons ->
       let kind = translateType ty
           descr = DataTypeDescr core_name kind
                   (map (translateDataConDecl tenv core_name . unLoc) data_cons)
       in insertDataType descr
  where
    core_name = toVar name

createCoreTable (Module decls) =
  let tenv = foldr ($) wiredInTypeEnv $ map translate decls
      translate ldecl = translateDecl tenv (unLoc ldecl)
  in tenv
