{-| The second pass of Core code generation.  All definitions of type-level
    entities are translated into Core.
-}

module CParser2.GenCode.Type where

import Control.Applicative
import Control.Monad
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid

import Common.Error
import Common.Identifier
import Common.Label
import Common.MonadLogic
import Common.SourcePos
import Common.Supply
import CParser2.AST
import CParser2.GenCode.Util
import CParser2.GenCode.Kind
import qualified Type.Error as Type
import Type.Environment
import qualified Type.Eval as Type
import qualified Type.Type as Type
import Type.Var

data VarAttrs =
  VarAttrs
  { isConlike :: !Bool          -- ^ @True@ if conlike
  }

-- | Extract information from an attribute list on a variable declaration
fromVarAttrs :: [Attribute Resolved] -> VarAttrs
fromVarAttrs attrs =
  -- Start with default attributes and modify given each attribute
  foldl' interpret empty_attrs attrs
  where
    empty_attrs = VarAttrs False

    interpret st ConlikeAttr = st {isConlike = True}

    -- Ignore inlining attributes
    interpret st InlineAttr = st
    interpret st InlineNeverAttr = st
    interpret st InlineSequentialAttr = st
    interpret st InlineFinalAttr = st
    interpret st InlinePostfinalAttr = st

    -- Ignore builtin attribute
    interpret st BuiltinAttr = st

    interpret st _ =
      error "Unexpected attribute on type declaration"

-- | Ensure that only permitted attributes appear on a type declaration
checkTypeAttrs :: [Attribute Resolved] -> ()
checkTypeAttrs attrs =
  foldl' seq () $ map check attrs
  where
    -- Ignore builtin attribute
    check BuiltinAttr = ()
    check _ =
      error "Unexpected attribute on type declaration"

-- | Convert to a base kind, with error checking
toBaseKind :: SourcePos -> Type.Kind -> TransT Type.BaseKind
toBaseKind pos k = do
  k' <- Type.reduceToWhnf k
  case k' of
    Type.VarT v | v == Type.boxV  -> return Type.BoxK
                | v == Type.bareV -> return Type.BareK
                | v == Type.valV  -> return Type.ValK
                | v == Type.outV  -> return Type.OutK
    _ -> Type.throwTypeError $ Type.UninhabitedError pos Type.KindLevel k

genTypes ts = mapAndUnzipM genType ts

-- | Translate an AST type to a core type and compute its kind.
--   Kind errors are detected.
genType :: RLType -> TransT (Type.Type, Type.Kind)
genType lty =
  case unLoc lty
  of VarT v -> do
       -- Look up this type, if it's a @let type@ synonym
       mtype <- lookupLetTypeSynonym v
       let t = fromMaybe (Type.VarT (toVar v)) mtype
       k <- liftTypeEvalM $ Type.typeCheckType t
       return (t, k)

     IntIndexT n -> return (Type.IntT n, Type.intindexT)

     TupleT tuple_args -> do
       -- Get types and kinds of type arguments
       (ts, ks) <- genTypes tuple_args
       base_ks <- forM ks $ \k -> do
         base_kind <- toBaseKind pos k
         return $! case base_kind
                   of Type.BoxK -> Type.BoxK
                      Type.ValK -> Type.ValK
                      _ -> internalError "genType: Not a valid tuple field type"
       return (Type.typeApp (Type.UTupleT base_ks) ts, Type.valT)

     AppT op arg -> do
       (op', op_k) <- genType op
       (arg', arg_k) <- genType arg
       result_k <-
         liftTypeEvalM $ Type.typeOfApp (getSourcePos lty) 1 op_k arg_k
       return (Type.AppT op' arg', result_k)

     FunT dom rng -> do
       (op', op_k) <- genType dom
       (rng', rng_k) <- genType rng

       -- Domain and range must not have arrow kind
       when (Type.getLevel op_k == Type.KindLevel) $ void $ do
         toBaseKind pos op_k
         toBaseKind pos rng_k

       return (Type.FunT op' rng', Type.boxT)

     AllT dom rng -> domain (getSourcePos lty) dom $ \dom' -> do
       (rng', rng_k) <- genType rng
       
       -- Range must not have arrow kind
       toBaseKind pos rng_k

       return (Type.AllT dom' rng', rng_k)

     LamT doms body ->
       withMany (domain $ getSourcePos lty) doms $ \doms' -> do
         (body', body_k) <- genType body

         let ty = map Type.binderType doms' `Type.funType` body_k
         return (build_lambda doms' body', ty)

     CoT kind dom rng -> do
       kind' <- genKind kind
       (dom', dom_k) <- genType dom
       (rng', rng_k) <- genType rng
       return (Type.typeApp (Type.CoT kind') [dom', rng'], Type.valT)
  where
    pos = getSourcePos lty

    -- Create a type function \dom1. (\dom2. ... (\domN. range))
    build_lambda doms range = foldr Type.LamT range doms

-- | Translate a type binding
domain :: SourcePos -> Domain Resolved -> (Type.Binder -> TransT a) -> TransT a
domain _ (Domain param (Just ty)) k = do
  let v = toVar param
  kind <- genKind ty
  assume v kind $ k (v Type.::: kind)

domain pos (Domain _ Nothing) _ =
  -- This error should have been caught during parsing
  internalError $ show pos ++ ": Missing type annotation in domain"

-- | Translate a list of domains that must have explicit types
domains :: SourcePos -> [Domain Resolved] -> ([Type.Binder] -> TransT a)
        -> TransT a
domains pos = withMany (domain pos)

translateDataConDecl :: Var -> Located (DataConDecl Resolved)
                     -> TransT DataConDescr
translateDataConDecl data_type_con (L pos decl) =
  domains pos (dconExTypes decl) $ \ex_types -> do
    args_and_kinds <- mapM genType $ dconArgs decl
    base_kinds <- mapM (toBaseKind pos . snd) args_and_kinds
    let fields = zip (map fst args_and_kinds) base_kinds
        dcon_var = toVar $ dconVar decl
    return (DataConDescr dcon_var ex_types fields)

varEnt :: Var -> LType Resolved -> [Attribute Resolved] -> TransT UpdateTypeEnv
varEnt ident ty attrs = do
  let !(VarAttrs conlike) = fromVarAttrs attrs
  (ty', _) <- genType ty

  let update1 = UpdateTypeEnv (\env -> insertGlobalTypeWithProperties env ident ty' conlike)
  return update1

typeEnt ident kind attrs = do
  kind' <- genKind kind

  -- Look up the type function by its name
  let name = case varName ident
             of Just l -> labelLocalNameAsString l
  type_function <- lookupBuiltinTypeFunction name
  return $ UpdateTypeEnv
    (\env -> case  type_function
             of Nothing -> insertGlobalType env ident kind'
                Just f -> insertTypeFunction env ident kind' f)

dataEnt pos core_name dom kind data_cons attrs = do
  kind' <- genKind kind
  let abstract = AbstractAttr `elem` attrs
      algebraic = not $ NonalgebraicAttr `elem` attrs

  domains pos dom $ \params -> do
    data_con_descrs <-
      mapM (translateDataConDecl core_name) data_cons
    base_kind <- toBaseKind pos kind'
    let descr = DataTypeDescr core_name params base_kind data_con_descrs abstract algebraic
    return $ UpdateTypeEnv (\env -> insertDataType env descr)

entity core_name _ (VarEnt ty attrs) = varEnt core_name ty attrs
entity core_name _ (TypeEnt ty attrs) = typeEnt core_name ty attrs
entity core_name pos (DataEnt dom ty data_cons attrs) =
  dataEnt pos core_name dom ty data_cons attrs

-- Translate only the types of functions and constants
entity core_name _ (FunEnt (L pos f) attrs) =
  varEnt core_name (funType pos showResolvedVar f) attrs
entity core_name _ (ConstEnt ty _ attrs) =
  varEnt core_name ty attrs
         
-- | Translate a global type-related declaration.
typeLevelDecls :: [LDecl Resolved] -> TransT UpdateTypeEnv
typeLevelDecls ldecls = go mempty ldecls
  where
    go updates (L pos (Decl ident ent) : ldecls) =
      case ent
      of TypeSynEnt ty -> do
           -- Expand the type synonym
           (ty', _) <- genType ty 
           withLetTypeSynonym ident ty' $ go updates ldecls
         _ -> do
           -- Process this entity and decide how to update the type environment
           upd <- entity core_name pos ent
           go (updates `mappend` upd) ldecls
      where
        core_name = toVar ident

    go updates [] = return updates

-- | Create a type environment from the given declarations
declTypeEnvironment :: RModule -> TransT UpdateTypeEnv
declTypeEnvironment (Module decls) = typeLevelDecls decls

typeTranslation :: IdentSupply Var
                -> [(Var, Type.Type)]
                -> TypeEnv
                -> Map.Map String BuiltinTypeFunction
                -> RModule
                -> IO TypeEnv
typeTranslation var_ids type_synonyms kind_env type_functions mod = do
  type_env_updates <-
    runTypeTranslation var_ids kind_env type_synonyms type_functions $
    declTypeEnvironment mod

  -- Create a new type environment to hold all definitions
  tenv <- mkWiredInTypeEnv
  applyUpdates type_env_updates tenv
  return tenv