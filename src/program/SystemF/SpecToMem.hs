{-| Convert a module from specification types to memory types.

The conversion is performed in a single pass over a module. 
-}

module SystemF.SpecToMem(convertSpecToMemTypes)
where

import Builtins.Builtins
import SystemF.Syntax
import SystemF.MemoryIR
import Type.Type

convertKind :: Type -> Type
convertKind (k1 `FunT` k2) =
  convertKind k1 `FunT` convertKind k2

convertKind (VarT v)
  | v == writeV = boxT          -- Writers become functions
  | otherwise   = VarT v        -- Other kinds are unchanged

convertType :: Type -> Type
convertType ty
  | Just (op, [arg]) <- fromVarApp ty,
    op `isPyonBuiltin` the_Writer =
      let arg' = convertType arg
      in varApp (pyonBuiltin the_OutPtr) [arg'] `FunT`
         varApp (pyonBuiltin the_IEffect) [arg']

  | otherwise =
      case ty
      of VarT _ -> ty
         IntT _ -> ty
         AppT op arg -> AppT (convertType op) (convertType arg)
         FunT dom rng -> FunT (convertType dom) (convertType rng)
         LamT (a ::: k) rng -> LamT (a ::: convertKind k) (convertType rng)
         AllT (a ::: k) rng -> AllT (a ::: convertKind k) (convertType rng)
         AnyT k -> AnyT (convertKind k)

convertTypM (TypM t) = TypM (convertType t)

convertTyParam (TyPatM (v ::: k)) =
  TyPatM (v ::: convertKind k)

convertParam :: PatM -> PatM
convertParam (MemVarP (v ::: t) _) =
  memVarP (v ::: convertType t)

convertExp :: ExpM -> ExpM
convertExp (ExpM expression) =
  case expression
  of VarE {} -> ExpM expression
     LitE {} -> ExpM expression
     AppE inf op ty_args args ->
       ExpM $ AppE inf
       (convertExp op) (map convertTypM ty_args) (map convertExp args)
     LamE inf f ->
       ExpM $ LamE inf (convertFun f)
     LetE inf b rhs body ->
       ExpM $ LetE inf (convertParam b) (convertExp rhs) (convertExp body)
     LetfunE inf defs body ->
       ExpM $ LetfunE inf (fmap convertDef defs) (convertExp body)
     CaseE inf scr alts ->
       ExpM $ CaseE inf (convertExp scr) (map convertAlt alts)
     ExceptE inf ty ->
       ExpM $ ExceptE inf (convertType ty)

convertAlt :: AltM -> AltM
convertAlt (AltM alt) =
  AltM $ alt { altTyArgs = map convertTypM $ altTyArgs alt
             , altExTypes = map convertTyParam $ altExTypes alt
             , altParams = map convertParam $ altParams alt
             , altBody = convertExp $ altBody alt}

convertFun :: FunM -> FunM
convertFun (FunM f) =
  FunM $ f { funTyParams = map convertTyParam $ funTyParams f
           , funParams = map convertParam $ funParams f
           , funReturn = convertTypM $ funReturn f
           , funBody = convertExp $ funBody f}

convertDef :: Def Mem -> Def Mem
convertDef def = mapDefiniens convertFun def

convertExport :: Export Mem -> Export Mem
convertExport e = e {exportFunction = convertFun $ exportFunction e}

convertSpecToMemTypes :: Module Mem -> Module Mem
convertSpecToMemTypes (Module mod_name defss exports) =
  Module mod_name (map (fmap convertDef) defss) (map convertExport exports)