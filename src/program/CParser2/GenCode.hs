
module CParser2.GenCode (createCoreFunctions) where

import Common.SourcePos
import Common.Error
import Common.Label
import Builtins.Builtins
import CParser2.AST
import qualified SystemF.Syntax as SystemF
import qualified SystemF.MemoryIR as SystemF
import Type.Environment
import Type.Var
import Type.Type(Binder(..), Level(..))
import qualified Type.Type as Type

-- | Extract function declarations from a module
checkModule :: Module Resolved -> Module Resolved
checkModule mod@(Module decls) 
  | any (not . is_fun_decl) decls =
      internalError "Expecting function declarations only"
  | otherwise = mod
  where
    is_fun_decl ldecl =
      case unLoc ldecl
      of Decl _ (FunEnt _) -> True
         _                 -> False

-------------------------------------------------------------------------------

toVar (ResolvedVar v _) = v

translateDomain :: Domain Resolved -> Type.Binder
translateDomain (Domain param ty) = toVar param ::: translateType ty

-- | Translate an AST type to a 'mem' type.
--   First the type is translated to a 'spec' type, then 
--   it's converted to 'mem'.
translateType :: RLType -> Type.Type
translateType t = specToMemType $ translateType' t

-- | Translate an AST type to a specification type.  This function is
--   only used by 'translateType'.
translateType' :: RLType -> Type.Type
translateType' lty =
  case unLoc lty
  of VarT v -> Type.VarT (toVar v)
     IntIndexT n -> Type.IntT n
     AppT op arg ->
       Type.AppT (translateType' op) (translateType' arg)
     FunT dom rng ->
       Type.FunT (translateType' dom) (translateType' rng)
     AllT (Domain param ty) rng ->
       Type.AllT (toVar param ::: translateType' ty) (translateType' rng)

translateFun pos f =
  SystemF.FunM $
  SystemF.Fun { SystemF.funInfo = SystemF.mkExpInfo pos
              , SystemF.funTyParams =
                map (SystemF.TyPatM . translateDomain) $ fTyParams f
              , SystemF.funParams =
                map (SystemF.patM . translateDomain) $ fParams f
              , SystemF.funReturn = SystemF.TypM $ translateType $ fRange f
              , SystemF.funBody = translateExp $ fBody f}

translateExp (L pos expression) =
  SystemF.ExpM $
  case expression
  of VarE v ->
       SystemF.VarE inf (toVar v)
     IntE n ->
       SystemF.LitE inf (SystemF.IntL n (Type.VarT $ pyonBuiltin the_int))
     TAppE op arg ->
       let (op', args) = uncurryTypeApp op [arg]
           op_exp = translateExp op'
           arg_types = map (SystemF.TypM . translateType) args
       in SystemF.AppE inf op_exp arg_types []
     AppE op arg ->
       let (op', ty_args, args) = uncurryApp op [arg]
           op_exp = translateExp op'
           arg_types = map (SystemF.TypM . translateType) ty_args
           arg_exps = map translateExp args
       in SystemF.AppE inf op_exp arg_types arg_exps
     LamE f ->
       SystemF.LamE inf (translateFun pos f)
     CaseE s alts ->
       SystemF.CaseE inf (translateExp s) (map (translateAlt . unLoc) alts)
     LetE binder rhs body ->
       SystemF.LetE inf (SystemF.patM $ translateDomain binder) (translateExp rhs) (translateExp body)
     LetfunE defs body ->
       let defgroup = SystemF.Rec [SystemF.mkDef (toVar v) (translateFun pos f)
                                  | L pos (Def v f) <- defs]
       in SystemF.LetfunE inf defgroup (translateExp body)
     ExceptE t ->
       SystemF.ExceptE inf (translateType t)
  where
    inf = SystemF.mkExpInfo pos

uncurryTypeApp e ty_args =
  case unLoc e
  of TAppE op arg -> uncurryTypeApp op (arg : ty_args)
     _ -> (e, ty_args)

uncurryApp e args =
  case unLoc e
  of AppE op arg -> uncurryApp op (arg : args)
     _ -> case uncurryTypeApp e []
          of (op, ty_args) -> (op, ty_args, args)

translateAlt (Alt con ty_args ex_types fields body) =
  SystemF.AltM $
  SystemF.DeCon { SystemF.altConstructor = toVar con
                , SystemF.altTyArgs = map (SystemF.TypM . translateType) ty_args
                , SystemF.altExTypes = map (SystemF.TyPatM . translateDomain) ex_types
                , SystemF.altParams = map (SystemF.patM . translateDomain) fields
                , SystemF.altBody = translateExp body}

translateDecl tenv (L pos (Decl name (FunEnt (L fun_pos f)))) =
  let ResolvedVar v _ = name
  in SystemF.mkDef v (translateFun fun_pos f)

translateDecl _ _ =
  internalError "translateDecl"

-------------------------------------------------------------------------------

createCoreFunctions tenv mod =
  case checkModule mod
  of Module decls ->
       let defs = map (translateDecl tenv) decls
       in SystemF.Module builtinModuleName [] [SystemF.Rec defs] []
      