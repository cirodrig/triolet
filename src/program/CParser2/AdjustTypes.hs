
module CParser2.AdjustTypes
       (VariableNameTable,
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

isOutPtr :: Var -> Bool
isOutPtr v = v == outPtrV

isStore :: Var -> Bool
isStore v = v == storeV

-------------------------------------------------------------------------------
-- Convert mem types to spec types
--
-- Replace all types of the form (OutPtr a -> Store) by (Init a).
-- Discard all other occurrences of OutPtr and Store.
--
-- Insert the special type 'Init' and kind 'init' into the environment.
--
-- There's no need to transform kinds.  Since kinds only appear in
-- type variable bindings and data type definitions, and Init is not
-- a first-class type, the kind 'init' does not appear in any types.
-- (This is true even though the type 'Init' does appear.)
convertMemToSpec :: TypeEnvBase UnboxedMode -> TypeEnvBase SpecMode
convertMemToSpec env =
  insert_init_types $ specializeTypeEnv Just Just do_type env
  where
    insert_init_types env =
      insertType initV kindT $
      insertType initConV (bareT `FunT` initT) env

    do_type ty =
      case ty
      of VarT v 
           | isOutPtr v -> Nothing
           | isStore v -> Nothing
           | otherwise -> pure ty
         AppT t1 t2 -> AppT <$> do_type t1 <*> do_type t2
         LamT b t -> LamT b <$> do_type t
         FunT (AppT (VarT v1) t) (VarT v2)
           | isOutPtr v1 && isStore v2 -> do
               t' <- do_type t
               pure $ AppT (VarT initConV) t
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
  let v_Init      = initConV
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

convertSpecToSF :: VariableNameTable
                -> TypeEnvBase SpecMode -> TypeEnvBase FullyBoxedMode
convertSpecToSF tbl env =
  specializeTypeEnv do_base_kind do_kind do_type env
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

