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
  | v == initV = boxT          -- Initializers become functions
  | otherwise  = VarT v        -- Other kinds are unchanged

convertType :: Type -> Type
convertType ty
  | Just (op, [arg]) <- fromVarApp ty,
    op `isCoreBuiltin` The_Init =
      let arg' = convertType arg
      in varApp (coreBuiltin The_OutPtr) [arg'] `FunT`
         VarT (coreBuiltin The_Store)

  | otherwise =
      case ty
      of VarT _ -> ty
         IntT _ -> ty
         AppT op arg -> AppT (convertType op) (convertType arg)
         FunT dom rng -> FunT (convertType dom) (convertType rng)
         LamT (a ::: k) rng -> LamT (a ::: convertKind k) (convertType rng)
         AllT (a ::: k) rng -> AllT (a ::: convertKind k) (convertType rng)
         AnyT k -> AnyT (convertKind k)
         CoT k -> CoT k

convertBinder (v ::: k) = (v ::: convertKind k)

convertTyParam (TyPat (v ::: k)) = TyPat (v ::: convertKind k)

convertParam :: PatM -> PatM
convertParam (PatM (v ::: t) _) = patM (v ::: convertType t)

convertExp :: ExpM -> ExpM
convertExp (ExpM expression) =
  case expression
  of VarE {} -> ExpM expression
     LitE {} -> ExpM expression
     ConE inf con args ->
       ExpM $ ConE inf (convert_constructor con) (map convertExp args)
     AppE inf op ty_args args ->
       ExpM $ AppE inf
       (convertExp op) (map convertType ty_args) (map convertExp args)
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
     CoerceE inf from_t to_t b ->
       ExpM $ CoerceE inf (convertType from_t) (convertType to_t)
       (convertExp b)
     ArrayE inf ty es ->
       ExpM $ ArrayE inf (convertType ty) (map convertExp es)
  where
    convert_constructor decon =
      case decon
      of VarCon con_var ty_args ex_types ->
           VarCon con_var (map convertType ty_args) (map convertType ex_types)
         TupleCon ty_args ->
           TupleCon (map convertType ty_args)

convertAlt :: AltM -> AltM
convertAlt (AltM alt) =
  AltM $ alt { altCon = convert_constructor $ altCon alt
             , altParams = map convertParam $ altParams alt
             , altBody = convertExp $ altBody alt}
  where
    convert_constructor decon =
      case decon
      of VarDeCon con_var ty_args ex_types ->
           VarDeCon con_var (map convertType ty_args) (map convertBinder ex_types)
         TupleDeCon ty_args ->
           TupleDeCon (map convertType ty_args)

convertFun :: FunM -> FunM
convertFun (FunM f) =
  FunM $ f { funTyParams = map convertTyParam $ funTyParams f
           , funParams = map convertParam $ funParams f
           , funReturn = convertType $ funReturn f
           , funBody = convertExp $ funBody f}

convertDef :: FDef Mem -> FDef Mem
convertDef def = mapDefiniens convertFun def

convertData (Constant inf ty e) =
  Constant inf (convertType ty) (convertExp e)

convertGlobalDef def = mapDefiniens convertEntity def

convertEntity (FunEnt f) = FunEnt $ convertFun f
convertEntity (DataEnt d) = DataEnt $ convertData d

convertExport :: Export Mem -> Export Mem
convertExport e = e {exportFunction = convertFun $ exportFunction e}

convertSpecToMemTypes :: Module Mem -> Module Mem
convertSpecToMemTypes (Module mod_name [] defss exports) =
  Module mod_name [] (map (fmap convertGlobalDef) defss) (map convertExport exports)