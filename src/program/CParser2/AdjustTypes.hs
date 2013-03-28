
module CParser2.AdjustTypes
       (VariableNameTable,
        convertFromMemTypeEnv)
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
convertMemToSpec :: ITypeEnvBase UnboxedMode -> IO (ITypeEnvBase SpecMode)
convertMemToSpec unboxed_env = do
  mutable_env <- thawTypeEnv unboxed_env
  env' <- specializeTypeEnv Just Just do_type do_type mutable_env

  -- Insert initializer types
  insertGlobalType env' initV kindT
  insertGlobalType env' initConV (bareT `FunT` initT)
  runTypeEnvM env' freezeTypeEnv
  where
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

data SFInfo = SFInfo { sf_Init   :: !Var
                     , sf_Stored :: !Var
                     , sf_Ref    :: !Var
                     , sf_Boxed  :: !Var
                     , sf_AsBox  :: !Var
                     , sf_AsBare :: !Var
                     }

getSFInfo :: VariableNameTable -> SFInfo
getSFInfo tbl =
  let v_Init   = initConV
      v_Stored = lookupVariableByName tbl "Stored"
      v_Ref    = refV
      v_Boxed  = lookupVariableByName tbl "Boxed"
      v_AsBox  = lookupVariableByName tbl "AsBox"
      v_AsBare = lookupVariableByName tbl "AsBare"
  in SFInfo v_Init v_Stored v_Ref v_Boxed v_AsBox v_AsBare

isBoxedAdapterCon1 :: SFInfo -> Var -> Bool
isBoxedAdapterCon1 env v =
  v == sf_Boxed env || v == sf_AsBox env

isAdapterCon1 :: SFInfo -> Var -> Bool
isAdapterCon1 env v =
  v == sf_Init env || v == sf_Stored env || v == sf_Ref env || 
  v == sf_Boxed env || v == sf_AsBox env || v == sf_AsBare env

convertSpecToSF :: VariableNameTable
                -> ITypeEnvBase SpecMode -> IO (ITypeEnvBase FullyBoxedMode)
convertSpecToSF tbl env = do
  env' <- thawTypeEnv env
  env'' <- specializeTypeEnv do_base_kind do_kind do_type do_bound_type env'
  runTypeEnvM env'' freezeTypeEnv
  where
    ctx = getSFInfo tbl

    do_base_kind ValK      = Just BoxK
    do_base_kind BoxK      = Just BoxK
    do_base_kind BareK     = Just BoxK
    do_base_kind IntIndexK = Just IntIndexK
    do_base_kind _         = Nothing

    do_kind = specToSFKind
    do_type ty = specToSFType ctx False ty
    do_bound_type ty = specToSFType ctx True ty

specToSFKind  (FunT t1 t2) = FunT <$> specToSFKind t1 <*> specToSFKind t2
specToSFKind (VarT kind_var)
  | kind_var == boxV      = Just boxT
  | kind_var == bareV     = Just boxT
  | kind_var == valV      = Just boxT
  | kind_var == intindexV = Just intindexT
  | otherwise             = Nothing
specToSFKind _ = internalError "specToSFKind: Unexpected kind"

-- | To be usable by the frontend, a binder appearing inside a type
--   must bind a boxed type variable
specToSFBinder (v ::: k)
  | is_boxed_kind k = (v :::) <$> specToSFKind k
  | otherwise       = Nothing
  where
    is_boxed_kind (VarT v) = v == boxV
    is_boxed_kind (FunT k1 k2) = is_boxed_kind k1 && is_boxed_kind k2
    is_boxed_kind _ = False

-- | Convert a spec type to a fully boxed type.  Coercions are removed from
--   the type.
--   If 'expect_boxed', then the only permitted coercions at the head of
--   the type are coercions to boxed type.
--   Otherwise, any coercion is permitted.
--
--   It would really be helpful to check types when 'expect_boxed' is true,
--   since the frontend relies on assumptions about boxed types to generate
--   valid code.  Currently types aren't checked.
specToSFType :: SFInfo -> Bool -> Type -> Maybe Type
specToSFType ctx expect_boxed ty =
  case fromVarApp ty
  of Just (con, [arg])
       | if expect_boxed
         then isBoxedAdapterCon1 ctx con
         else isAdapterCon1 ctx con ->
           -- Remove any additional coercions appearing under this one
           do_type arg
     _ -> case ty
          of VarT v
               | isAdapterCon1 ctx v -> Nothing
               | otherwise -> pure ty
             AppT op arg -> AppT <$> do_type op <*> do_type arg
             LamT b body -> not_boxed $ LamT <$> specToSFBinder b <*> do_type body
             FunT arg ret -> FunT <$> boxed_type arg <*> boxed_type ret
             AllT b body -> AllT <$> specToSFBinder b <*> boxed_type body
             AnyT k -> AnyT <$> specToSFKind k
             IntT n -> not_boxed $ pure ty
             UTupleT _ -> Nothing
             CoT k  -> not_boxed $ CoT <$> specToSFKind k
  where
    -- Return something that is not a boxed type.
    -- Return 'Nothing' if a boxed type was expected
    not_boxed x = if expect_boxed then Nothing else x
    
    do_type ty = specToSFType ctx False ty
    boxed_type ty = specToSFType ctx True ty

-------------------------------------------------------------------------------
-- Generate Spec and fully boxed types

convertFromMemTypeEnv :: VariableNameTable
                      -> ITypeEnvBase UnboxedMode
                      -> IO (ITypeEnvBase SpecMode, ITypeEnvBase FullyBoxedMode)
convertFromMemTypeEnv tbl env = do
  spec_env <- convertMemToSpec env
  sf_env <- convertSpecToSF tbl spec_env
  return (spec_env, sf_env)
