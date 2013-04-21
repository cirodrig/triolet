{-| The first pass of Core code generation, which computes kinds for
    all type-level definitions in the module.
-}

module CParser2.GenCode.Kind(genKind, kindTranslation)
where

import Control.Applicative
import Control.Monad
import qualified Data.Map as Map
import Data.Monoid

import Common.Identifier
import Common.SourcePos
import Common.Supply
import CParser2.AST
import CParser2.GenCode.Util
import Type.Environment
import qualified Type.Type as Type
import Type.Var

-- | Translate an AST kind to a core kind
genKind :: RLType -> TransT Type.Kind
genKind (L pos rtype) =
  case rtype
  of VarT v -> do
       -- Look up this type, if it's a @let type@ synonym
       mtype <- lookupLetTypeSynonym v
       case mtype of 
         Just t -> return t
         Nothing -> return $ Type.VarT (toVar v)
     k1 `FunT` k2 ->
       Type.FunT <$> genKind k1 <*> genKind k2
     _ -> error $ show pos ++  ": Unexpected kind expression"

-- | Translate a global type-related declaration.
declKind :: LDecl Resolved -> TransT UpdateTypeEnv
declKind (L loc (Decl ident ent)) = do
  let make_update kind =
        return $ UpdateTypeEnv $ \env -> insertGlobalType env (toVar ident) kind
  case ent of
    TypeEnt k _           -> genKind k >>= make_update
    DataEnt binders k _ _ -> genKind (fun_kind binders k) >>= make_update
    _                     -> return mempty
  where
    fun_kind bs k = foldr fun_t k bs
      where
        fun_t (Domain _ (Just dom)) rng = L loc (dom `FunT` rng)

-- | Create a kind environment from the declarations in the module
moduleKindEnvironment :: RModule -> TransT UpdateTypeEnv
moduleKindEnvironment (Module decls) =
  liftM mconcat $ mapM declKind decls

-- | Compute the kinds of all type-level entities in the module.
--   These kinds are not part of the module that's finally generated.
--   They are needed while translating type-level entities into core.
kindTranslation :: IdentSupply Var
                -> [(Var, Type.Type)]
                -> Map.Map String BuiltinTypeFunction
                -> RModule
                -> IO TypeEnv
kindTranslation var_ids type_synonyms type_functions mod = do
  -- Create a type environment with built-in types to use
  -- while examining kinds
  tenv <- mkWiredInTypeEnv
  kind_env_updates <-
    runTypeTranslation var_ids tenv type_synonyms type_functions $
    moduleKindEnvironment mod

  -- Add bindings to the type environment
  applyUpdates kind_env_updates tenv
  return tenv