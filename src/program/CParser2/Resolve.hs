{-| Resolve names
-}

{-# LANGUAGE FlexibleInstances, ViewPatterns #-}
module CParser2.Resolve(globalEnvironment, resolveModule)
where

import Prelude hiding(sequence, mapM)
import Control.Applicative
import Control.Monad hiding(sequence, mapM)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.Traversable
import Debug.Trace

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.Supply
import Common.SourcePos
import Common.Label
import Type.Var
import Type.Type(Level(..), HasLevel(..))
import CParser2.AST

-------------------------------------------------------------------------------
-- Name resolution environments

-- | A dictionary maps parsed varible names to variables
type Dict = Map.Map (Identifier Parsed) (Identifier Resolved)

-- | The environment consisting of all variable names that are in scope.
--   It's organized as a sequence of nested scopes,
--   starting with the innermost.
--
--   The set of data and type constructor names is also tracked.
--   Redefining these is an error.
data Env = Env { envScopes             :: [Dict]
               , envConstructors       :: !(Set.Set (Identifier Parsed))
               }

modifyScopes :: ([Dict] -> [Dict]) -> Env -> Env
modifyScopes f env = env {envScopes = f $ envScopes env}

modifyHeadScope :: (Dict -> Dict) -> Env -> Env
modifyHeadScope f = modifyScopes on_head
  where
    on_head [] = internalError "modifyHeadScope: Empty environment"
    on_head (d:ds) = f d : ds

-- | Add a name to the environment.
addToEnv :: Identifier Parsed -> Identifier Resolved -> Env -> Env
addToEnv parsed_name resolved_var env =
  modifyHeadScope (Map.insert parsed_name resolved_var) env

-- | Search for a name in the environment
lookupInEnv :: Identifier Parsed -> Env -> Maybe (Identifier Resolved)
lookupInEnv name env = search (envScopes env) 
  where
    search (d:ds) = Map.lookup name d `mplus` search ds
    search []     = mzero

-------------------------------------------------------------------------------
-- Error messages

-- | An error message
type Error = String
type Errors = [String] -> [String]

noErrors :: Errors
noErrors = id

maybeError :: Maybe Error -> Errors
maybeError Nothing  = id
maybeError (Just e) = (e:)

-- | Get a list of all error messages.  The list is empty if there are no
--   errors.
getErrors :: Errors -> [String]
getErrors errs = errs []

-------------------------------------------------------------------------------
-- The name resolution monad

-- | Data that are global to name resolution.  These are never modified.
data Environment =
  Environment
  { varIDSupply      :: !(IdentSupply Var)
  , currentModule    :: !ModuleName
  }

-- | A monad used for name resolution.
newtype NR a = NR {runNR :: Environment -> Env -> IO (Maybe a, Env, Errors)}

returnNR x e = return (Just x, e, noErrors)

instance Functor NR where
  fmap f m = do x <- m
                return (f x)

instance Applicative NR where
  pure = return
  (<*>) = ap

instance Monad NR where
  return x = NR (\_ e -> returnNR x e)
  m >>= k = NR (\env names -> do (mx, e1, errs1) <- runNR m env names
                                 case mx of 
                                   Just x -> do
                                     (my, e2, errs2) <- runNR (k x) env e1
                                     return (my, e2, errs1 . errs2)
                                   Nothing -> return (Nothing, e1, errs1))

recover :: a -> NR a -> NR a
recover defl m = NR $ \env names -> do
  (result, e, errs) <- runNR m env names
  return (Just $ fromMaybe defl result, e, errs)

instance Supplies NR (Ident Var) where
  fresh = NR (\env e -> do
    s <- supplyValue (varIDSupply env)
    returnNR s e)
  supplyToST = internalError "Not implemented: (NR * Ident Var).supplyToST"

-- | Get the current module's name.
getModuleName :: NR ModuleName
getModuleName = NR (\env e -> returnNR (currentModule env) e)

getNames :: NR Env
getNames = NR (\_ names -> returnNR names names)

-- | Log an error if 'True' is given, otherwise do nothing.
--   Execution continues normally after the error is logged.
logErrorIf :: Bool -> Error -> NR ()
logErrorIf cond err =
  let merr = if cond then (err:) else id 
  in NR (\_ e -> return (Just (), e, merr))

-- | Log an error.
--   This doesn't interrupt execution; execution continues normally
--   after the error is logged.
logError :: Error -> NR ()
logError err = NR (\_ e -> return (Just (), e, (err:)))

failError :: Error -> NR a
failError err = NR (\_ e -> return (Nothing, e, (err:)))

-- | Enter a local scope.  Variables bound in this scope are
--   only visible within the scope.
enter :: NR a -> NR a
enter m = NR $ \env names -> do
    (x, _, errs) <- runNR m env (modifyScopes (Map.empty :) names)
    return (x, names, errs)

-- | Define a variable or constructor.  The variable is added to the
--   current scope, and can be looked up with 'use'.
--   This function is called through either 'def' or 'defCon'.
defineIdentifier :: Identifier Parsed -> Identifier Resolved -> NR ()
defineIdentifier parsed_name resolved_var =
  NR $ \env names ->
    let s = addToEnv parsed_name resolved_var names
    in returnNR () s

-- | Determine whether the given name is a constructor name
isConstructor :: Identifier Parsed -> NR Bool
isConstructor name =
  NR $ \env names ->
    let is_con = name `Set.member` envConstructors names
    in returnNR is_con names

-- | Define a variable.  Error if there's a constructor with this name.  
--   The variable is added to the current scope,
--   and can be looked up with 'use'.
def :: SourcePos -> Identifier Parsed -> Identifier Resolved -> NR ()
def pos parsed_name resolved_var = do
  is_con <- isConstructor parsed_name
  if is_con
    then failError $ show pos ++ ": Redefined constructor name " ++ parsed_name
    else defineIdentifier parsed_name resolved_var

-- | Define a constructor.  The variable is added to the current scope,
--   and can be looked up with 'use'.
defCon :: SourcePos -> Identifier Parsed -> Identifier Resolved -> NR ()
defCon _ = defineIdentifier

use :: Identifier Parsed -> SourcePos -> NR (Identifier Resolved)
use = fetch "Could not find:"

-- | Use a variable, but provide location information in case of an error.
--   The variable's level is checked, and must match the given level.
fetch :: String -> Identifier Parsed -> SourcePos -> NR (Identifier Resolved)
fetch error_header parsed_name pos = NR $ \env names ->
  let m_ident = lookupInEnv parsed_name names
      error_messages 
        | Nothing <- m_ident = [not_found]
        | otherwise = []
  in return (m_ident, names, (error_messages ++))
  where
    location = " (" ++ show pos ++ ")"
    not_found = error_header ++ " " ++ parsed_name ++ location

wrongLevelError pos name expected actual =
  let location = "(" ++ show pos ++ ")"
      e_level = show expected
      a_level = show actual
  in name ++ " has level " ++ a_level ++ ", expecting " ++ e_level ++ location

levelCheck :: SourcePos -> Level -> Level -> NR ()
levelCheck pos expected actual = logErrorIf (e_level /= a_level) message
  where
    location = "(" ++ show pos ++ ")"
    e_level = show expected
    a_level = show actual
    message = location ++ ": got level " ++ a_level ++ ", expecting " ++ e_level

-------------------------------------------------------------------------------
-- Name resolution

resolveL :: (SourcePos -> a -> NR b) -> Located a -> NR (Located b)
resolveL f (L pos x) = L pos <$> f pos x

resolveMaybe :: (a -> NR b) -> Maybe a -> NR (Maybe b) 
resolveMaybe f (Just x) = liftM Just $ f x
resolveMaybe _ Nothing  = return Nothing

-- | Create and define a new variable inhabiting the current module.
newRVarOrCon :: Bool -> SourcePos -> Level -> Identifier Parsed -> NR ResolvedVar
newRVarOrCon is_con pos lv parsed_name = do
  modname <- getModuleName
  id <- fresh
  let label = plainLabel modname parsed_name
      v = ResolvedVar (mkVar id (Just label) lv)
  if is_con
    then defCon pos parsed_name v
    else def pos parsed_name v
  return v

newRVar = newRVarOrCon False
newRCon = newRVarOrCon True

-- | Resolve a type expression.  The expression must have the specified level.
resolveLType :: Level -> PLType -> NR RLType
resolveLType level (L pos t) = do
  t' <- resolveType pos level t 
  return $ L pos t'

-- | Resolve a type expression.  Return the type and the inferred level.
--   The level is used for error checking.
resolveType :: SourcePos -> Level -> PType -> NR RType
resolveType pos level ty =
  case ty
  of VarT v -> do
       v' <- use v pos
       check_level $ getLevel v'
       return $ VarT v'
     IntIndexT n -> do
       check_level TypeLevel
       return $ IntIndexT n
     TupleT ts -> do
       check_level TypeLevel
       args <- mapM (resolveLType TypeLevel) ts
       return $ TupleT args
     AppT op arg -> do
       op' <- resolveLType level op
       arg' <- resolveLType level arg
       return $ AppT op' arg'
     FunT d r -> do
       d' <- resolveLType level d
       r' <- resolveLType level r
       return $ FunT d' r'
     AllT d r -> resolveDomain pos level d $ \d' -> do
       r' <- resolveLType level r
       return $ AllT d' r'
     LamT d r -> withMany (resolveDomain pos level) d $ \d' -> do
       r' <- resolveLType level r
       return $ LamT d' r'
     CoT k d r -> do
       check_level TypeLevel
       k' <- resolveLType KindLevel k
       d' <- resolveLType TypeLevel d
       r' <- resolveLType TypeLevel r
       return $ CoT k' d' r'
  where
    check_level actual_level = levelCheck pos level actual_level
    {-
    check_level lv =
      logErrorIf (lv == ObjectLevel) $
      "Term must be higher than Object level (" ++ show pos ++ ")" -}

-- | Resolve a variable binding.
--   The variable must have the specified level.
resolveDomain :: SourcePos -> Level -> Domain Parsed
              -> (Domain Resolved -> NR a) -> NR a
resolveDomain pos level (Domain binder t) k = do
  t' <- resolveMaybe (resolveLType (succ level)) t
  enter $ do binder' <- newRVar pos level binder
             k (Domain binder' t')

{-
-- | Resolve a variable binding, and also check its level.
resolveDomain' :: Level
               -> String
               -> SourcePos
               -> Domain Parsed
               -> (Domain Resolved -> NR a)
               -> NR a
resolveDomain' expected_level error_message pos d k = do
  (x, lv) <- resolveDomain d k
  logErrorIf (lv /= expected_level) $
    error_message ++ " (" ++ show pos ++ ")"
  return x
-}

resolveDomainT pos = resolveDomain pos TypeLevel

resolveDomainV pos = resolveDomain pos ObjectLevel

resolveExp :: SourcePos -> Exp Parsed -> NR (Exp Resolved)
resolveExp pos expression = 
  case expression
  of VarE v -> VarE <$> use v pos
     IntE n -> pure $ IntE n
     FloatE n -> pure $ FloatE n
     TupleE ts -> TupleE <$> mapM (resolveL resolveExp) ts
     TAppE e t -> do
       e' <- resolveL resolveExp e 
       t' <- resolveLType TypeLevel t
       return $ TAppE e' t'
     AppE e1 e2 -> AppE <$> resolveL resolveExp e1 <*> resolveL resolveExp e2
     LamE f -> LamE <$> resolveFun pos f
     LetE binder rhs body -> do
       rhs' <- resolveL resolveExp rhs
       resolveDomainV pos binder $ \binder' -> do
         body' <- resolveL resolveExp body
         return $ LetE binder' rhs' body'
     LetTypeE lhs rhs body -> do
       rhs' <- resolveLType TypeLevel rhs 
       enter $ do lhs' <- newRVar pos TypeLevel lhs
                  body' <- resolveL resolveExp body
                  return $ LetTypeE lhs' rhs' body'
     LetfunE defs e ->
       resolveDefGroup defs $ \defs' -> LetfunE defs' <$> resolveL resolveExp e
     CaseE scr alts -> CaseE <$> resolveL resolveExp scr <*>
                       mapM (resolveL resolveAlt) alts
     ExceptE t -> do
       t' <- resolveLType TypeLevel t
       return $ ExceptE t'
     
     CoerceE from_t to_t body -> do
       from_t' <- resolveLType TypeLevel from_t
       to_t' <- resolveLType TypeLevel to_t
       body' <- resolveL resolveExp body
       return $ CoerceE from_t' to_t' body'

resolveDefGroup :: [LDef Parsed] -> ([LDef Resolved] -> NR a) -> NR a
resolveDefGroup defs k = enter $ do
  -- Create a new variable for each local variable
  resolved <- sequence [newRVar pos ObjectLevel (dName d) | L pos d <- defs]
  
  -- Process local functions and pass them to the continuation
  k =<< zipWithM resolve_def resolved defs
  where
    resolve_def new_var (L pos (Def _ f attrs)) = do
      f' <- resolveFun pos f
      return $ L pos (Def new_var f' attrs)

resolveAlt :: SourcePos -> Alt Parsed -> NR (Alt Resolved)
resolveAlt pos (Alt pattern body) = do
  resolvePattern pos pattern $ \pattern' -> do
    body' <- resolveL resolveExp body
    return $ Alt pattern' body'

resolvePattern pos (ConPattern con ex_types fields) k = do
  con' <- use con pos
  withMany (resolveDomainT pos) ex_types $ \ex_types' ->
    withMany (resolvePattern pos) fields $ \fields' ->
    k (ConPattern con' ex_types' fields')

resolvePattern pos (TuplePattern fields) k =
    withMany (resolvePattern pos) fields $ \fields' ->
    k (TuplePattern fields')

resolvePattern pos (VarPattern dom) k =
  resolveDomainV pos dom $ \dom' -> k (VarPattern dom')

resolvePattern pos (ConOrVarPattern ident) k =
  ifM (isConstructor ident)
  (resolvePattern pos (ConPattern ident [] []) k)
  (resolvePattern pos (VarPattern (Domain ident Nothing)) k)

resolveFun :: SourcePos -> PFun -> NR RFun
resolveFun pos f =
  withMany (resolveDomainT pos) (fTyParams f) $ \tparams ->
  withMany (resolveDomainV pos) (fParams f) $ \params -> do
    range <- resolveLType TypeLevel $ fRange f
    body <- resolveL resolveExp $ fBody f
    return $ Fun tparams params range body  

resolveDataConDecl :: SourcePos
                   -> ResolvedVar -- ^ The resolved data constructor
                   -> DataConDecl Parsed
                   -> NR (DataConDecl Resolved)
resolveDataConDecl pos v' (DataConDecl _ ex_types args) = do
  enter $
    withMany (resolveDomainT pos) ex_types $ \ex_types' -> do
      args' <- mapM (resolveLType TypeLevel) args
      return $ DataConDecl v' ex_types' args'

resolveEntity :: SourcePos -> ResolvedDeclName -> Entity Parsed
              -> NR (Entity Resolved)
resolveEntity _ _ (VarEnt ty attrs) = do
  ty' <- resolveLType TypeLevel ty
  return $ VarEnt ty' attrs

resolveEntity _ (GlobalName r_name) (TypeEnt ty) = do
  ty' <- resolveLType KindLevel ty
  return $ TypeEnt ty'

resolveEntity _ (GlobalName r_name) (TypeSynEnt ty) = do
  ty' <- resolveLType TypeLevel ty
  return $ TypeSynEnt ty'

resolveEntity pos (DataConNames _ data_con_names) (DataEnt params ty cons attrs) = do
  ty' <- resolveLType KindLevel ty
  withMany (resolveDomainT pos) params $ \params' -> do
    cons' <- sequence [L pos <$> resolveDataConDecl pos v con
                      | (v, L pos con) <- zip data_con_names cons]
    return $ DataEnt params' ty' cons' attrs

resolveEntity _ _ (ConstEnt ty e attrs) = do
  ty' <- resolveLType TypeLevel ty
  e' <- resolveL resolveExp e
  return $ ConstEnt ty' e' attrs

resolveEntity _ _ (FunEnt f attrs) = do
  f' <- resolveL resolveFun f
  return $ FunEnt f' attrs

-- | Resolve a global declaration.  The declared variable should be in the
--   environment already.
resolveDecl :: ResolvedDeclName -> PLDecl -> NR RLDecl
resolveDecl r_name (L pos (Decl _ ent)) = do
  r_ent <- resolveEntity pos r_name ent
  return $ L pos (Decl (resolvedGlobal r_name) r_ent)

data ResolvedDeclName =
    GlobalName {resolvedGlobal :: ResolvedVar}
  | DataConNames {resolvedGlobal :: ResolvedVar,
                  resolvedDataConstructors :: [ResolvedVar]}

resolveDeclName (L pos (Decl name ent)) =
  case ent
  of VarEnt {}                  -> object_level_var
     TypeEnt {}                 -> type_level_con
     TypeSynEnt {}              -> type_level_var
     DataEnt _ _ constructors _ -> data_definition constructors
     ConstEnt {}                -> object_level_var
     FunEnt {}                  -> object_level_var
  where
    object_level_var = liftM GlobalName $ newRVar pos ObjectLevel name
    type_level_con = liftM GlobalName $ newRCon pos TypeLevel name
    type_level_var = liftM GlobalName $ newRVar pos TypeLevel name
    data_definition constructors = do
      tycon <- newRCon pos TypeLevel name
      datacons <- sequence [newRCon pos ObjectLevel $ dconVar d
                           | L _ d <- constructors]
      return $ DataConNames tycon datacons

-- | Resolve top-level declarations, with limited error recovery
resolveDecls decls = do
  -- Create a new variable for each global variable and data constructor
  r_names <- mapM resolveDeclName decls

  -- Resolve the declarations, recovering from errors
  r_decls <- sequence [recover Nothing $ liftM Just (resolveDecl name decl) 
                      | (name, decl) <- zip r_names decls]
  return $ catMaybes r_decls

resolveModule' (Module decls) = Module <$> resolveDecls decls

-- | Construct a global environment that maps predefined variable names
--   to predefined variables.
globalEnvironment :: [(String, Var)]
                  -> (Map.Map (Identifier Parsed) ResolvedVar)
globalEnvironment xs = Map.fromList $ map mk_var xs
  where
    mk_var (name, sf_var) = (name, ResolvedVar sf_var)

-- | Get data constructor, type constructor, and type function names.
--   These names may not be redefined as variables, and they are checked
--   against definitions during name resolution.
constructorNames :: PModule -> [Identifier Parsed]
constructorNames (Module decls) =
  concatMap decl_constructor_names decls
  where
    decl_constructor_names ldecl =
      case unLoc ldecl
      of Decl name ent ->
           case ent
           of DataEnt _ _ con_decls _ ->
                let con_names = map data_con_name con_decls
                in name : con_names
              TypeEnt _ ->
                [name]
              _ ->
                []

    data_con_name ldecl = dconVar $ unLoc ldecl

resolveModule :: IdentSupply Var -- ^ Supply of unique variable IDs
              -> Map.Map (Identifier Parsed) ResolvedVar
              -> ModuleName     -- ^ Name of module being processed
              -> PModule       -- ^ The parsed module
              -> IO RModule
resolveModule id_supply predef modname mod = do
  let init_environment = Environment id_supply modname
      constructor_names = Set.fromList $ constructorNames mod
      init_env = Env [predef] constructor_names
  (mod', env, errors) <- runNR (resolveModule' mod) init_environment init_env
  case getErrors errors of
    [] -> case mod' of Just m -> return m
    es -> do mapM_ putStrLn es
             fail "Name resolution failed"
