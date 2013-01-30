
module CParser2.AdjustTypes
       (VariableNameTable,
        expandInitTypeInModule,
        expandInitType,
        toMemEnv,
        convertMemToSpec,
        convertSpecToSF)
where
  
import Control.Applicative
import qualified Data.Map as Map

import Common.Error
import SystemF.Syntax
import SystemF.MemoryIR
import Type.Environment
import Type.Type

type VariableNameTable = Map.Map String Var

lookupVariableByName :: VariableNameTable -> String -> Var
lookupVariableByName tbl name =
  case Map.lookup name tbl
  of Just v -> v
     Nothing -> internalError $ "lookupVariableByName: " ++ name

-- | Hold some type constructors in variables so we can use them.
data Info = Info { var_Init   :: !Var
                 , var_OutPtr :: !Var
                 , var_Store  :: !Var
                 }

getInfo :: VariableNameTable -> Info
getInfo tbl =
  let v_Init   = lookupVariableByName tbl "Init"
      v_OutPtr = lookupVariableByName tbl "OutPtr"
      v_Store  = lookupVariableByName tbl "Store"
  in Info v_Init v_OutPtr v_Store

isInit :: Info -> Var -> Bool
isInit ctx v = var_Init ctx == v

isOutPtr :: Info -> Var -> Bool
isOutPtr ctx v = var_OutPtr ctx == v

isStore :: Info -> Var -> Bool
isStore ctx v = var_Store ctx == v

-------------------------------------------------------------------------------
-- Expand the 'Init' type in a module.
-- Wherever 'Init a' appears, replace it with 'Out a -> Store'.

expandTypes ctx ts = map (expandType ctx) ts

expandType :: Info -> Type -> Type
expandType ctx ty
  | Just (op, [arg]) <- fromVarApp ty, isInit ctx op =
      let arg' = expandType ctx arg
      in varApp (var_OutPtr ctx) [arg'] `FunT` VarT (var_Store ctx)

  | otherwise =
      case ty
      of VarT v
           | isInit ctx v -> internalError "expandType: Unexpected 'Init'"
           | otherwise -> ty
         AppT op arg -> AppT (continue op) (continue arg)
         FunT dom rng -> FunT (continue dom) (continue rng)
         LamT (a ::: k) rng -> LamT (a ::: k) (continue rng)
         AllT (a ::: k) rng -> AllT (a ::: k) (continue rng)
         AnyT k -> AnyT k
         IntT _ -> ty
         CoT _ -> ty
         UTupleT _ -> ty
  where
    continue t = expandType ctx t

expandParams ctx p = map (expandParam ctx) p

expandParam :: Info -> PatM -> PatM
expandParam ctx (PatM (v ::: t) _) = patM (v ::: expandType ctx t)

expandExps ctx es = map (expandExp ctx) es

expandExp :: Info -> ExpM -> ExpM
expandExp ctx exp = mapExpTypes id (expandType ctx) exp

expandFun :: Info -> FunM -> FunM
expandFun ctx f = mapFunTypes id (expandType ctx) f

expandDef :: Info -> FDef Mem -> FDef Mem
expandDef ctx def = mapDefiniens (expandFun ctx) def

expandData ctx (Constant inf ty e) =
  Constant inf (expandType ctx ty) (expandExp ctx e)

expandGlobalDef ctx def = mapDefiniens (expandEntity ctx) def

expandEntity ctx (FunEnt f) = FunEnt $ expandFun ctx f
expandEntity ctx (DataEnt d) = DataEnt $ expandData ctx d

expandExport :: Info -> Export Mem -> Export Mem
expandExport ctx e = e {exportFunction = expandFun ctx $ exportFunction e}

expandInitTypeInModule :: VariableNameTable -> Module Mem -> Module Mem
expandInitTypeInModule tbl mod =
  let ctx = getInfo tbl
      Module mod_name [] defss exports = mod
      defss' = map (fmap (expandGlobalDef ctx)) defss
      exports' = map (expandExport ctx) exports
  in Module mod_name [] defss' exports'

-------------------------------------------------------------------------------

expandInitType :: VariableNameTable -> SpecTypeEnv -> SpecTypeEnv
expandInitType tbl env =
  let ctx = getInfo tbl
  in specializeTypeEnv id Just Just (Just . expandType ctx) env

-------------------------------------------------------------------------------

toMemEnv :: VariableNameTable -> SpecTypeEnv -> TypeEnv
toMemEnv tbl env =
  specializeTypeEnv builtinMemTypeFunction Just Just Just env

-------------------------------------------------------------------------------
-- Convert mem types to spec types
--
-- Replace all types of the form (OutPtr a -> Store) by (Init a).
-- Discard all other occurrences of OutPtr and Store.
--
-- There's no need to transform kinds.  Since kinds only appear in
-- type variable bindings and data type definitions, and Init is not
-- a first-class type, the kind 'init' does not appear in any types.
-- (This is true even though the type 'Init' does appear.)
convertMemToSpec :: VariableNameTable -> SpecTypeEnv -> SpecTypeEnv
convertMemToSpec tbl env = 
  specializeTypeEnv id Just Just do_type env
  where
    ctx = getInfo tbl
    do_type ty =
      case ty
      of VarT v 
           | isOutPtr ctx v -> Nothing
           | isStore ctx v -> Nothing
           | otherwise -> pure ty
         AppT t1 t2 -> AppT <$> do_type t1 <*> do_type t2
         LamT b t -> LamT b <$> do_type t
         FunT (AppT (VarT v1) t) (VarT v2)
           | isOutPtr ctx v1 && isStore ctx v2 -> do
               t' <- do_type t
               pure $ AppT (VarT $ var_Init ctx) t
         FunT d r -> FunT <$> do_type d <*> do_type r
         AllT b t -> AllT b <$> do_type t
         AnyT t -> AnyT <$> do_type t
         IntT n -> pure $ IntT n
         CoT k -> pure $ CoT k
         UTupleT ks -> pure $ UTupleT ks

-------------------------------------------------------------------------------

data SFInfo = SFInfo { sf_Init      :: !Var
                     , sf_Stored    :: !Var
                     , sf_Ref       :: !Var
                     , sf_Boxed     :: !Var
                     , sf_BoxedType :: !Var
                     , sf_BareType  :: !Var
                     }

getSFInfo :: VariableNameTable -> SFInfo
getSFInfo tbl =
  let v_Init      = lookupVariableByName tbl "Init"
      v_Stored    = lookupVariableByName tbl "Stored"
      v_Ref       = lookupVariableByName tbl "Ref"
      v_Boxed     = lookupVariableByName tbl "Boxed"
      v_BoxedType = lookupVariableByName tbl "AsBox"
      v_BareType  = lookupVariableByName tbl "AsBare"
  in SFInfo v_Init v_Stored v_Ref v_Boxed v_BoxedType v_BareType

isAdapterCon1 :: SFInfo -> Var -> Bool
isAdapterCon1 env v =
  v == sf_Init env || v == sf_Stored env || v == sf_Ref env || 
  v == sf_Boxed env || v == sf_BoxedType env || v == sf_BareType env

convertSpecToSF :: VariableNameTable -> SpecTypeEnv -> TypeEnv
convertSpecToSF tbl env =
  specializeTypeEnv builtinPureTypeFunction do_base_kind do_kind do_type env
  where
    ctx = getSFInfo tbl

    do_base_kind ValK      = Just BoxK
    do_base_kind BoxK      = Just BoxK
    do_base_kind BareK     = Just BoxK
    do_base_kind IntIndexK = Just IntIndexK
    do_base_kind _         = Nothing

    do_kind (FunT t1 t2) = FunT <$> do_kind t1 <*> do_kind t2
    do_kind (VarT kind_var)
      | kind_var == boxV      = Just boxT
      | kind_var == bareV     = Just boxT
      | kind_var == valV      = Just boxT
      | kind_var == intindexV = Just intindexT
      | otherwise             = Nothing
    do_kind _ = internalError "convertSpecToSF: Unexpected kind"

    do_type ty =
      case fromVarApp ty
      of Just (con, [arg])
          | isAdapterCon1 ctx con -> do_type arg
         _ -> case ty
              of VarT v 
                   | isAdapterCon1 ctx v -> Nothing
                   | otherwise -> pure ty
                 AppT op arg -> AppT <$> do_type op <*> do_type arg
                 LamT b body -> LamT <$> do_binder b <*> do_type body
                 FunT arg ret -> FunT <$> do_type arg <*> do_type ret
                 AllT b body -> AllT <$> do_binder b <*> do_type body
                 AnyT k -> AnyT <$> do_kind k
                 IntT n -> pure ty
                 UTupleT _ -> Nothing
                 CoT k -> CoT <$> do_kind k

    do_binder (v ::: k) = (v :::) <$> do_kind k

