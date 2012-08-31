{-| Resolve names
-}

{-# LANGUAGE FlexibleInstances, ViewPatterns #-}
module CParser2.Resolve(globalEnvironment, resolveModule)
where

import Prelude hiding(sequence, mapM)
import Control.Applicative
import Control.Monad hiding(sequence, mapM)
import qualified Data.Map as Map
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
type Env = [Dict]

-- | Add a name to the environment
addToEnv :: Identifier Parsed -> Identifier Resolved -> Env -> Env
addToEnv parsed_name resolved_var (d:ds) =
  Map.insert parsed_name resolved_var d : ds

addToEnv _ _ [] = error "addToEnv: Empty environment"


-- | Search for a name in the environment
lookupInEnv :: Identifier Parsed -> Env -> Maybe (Identifier Resolved)
lookupInEnv name (d:ds) = Map.lookup name d `mplus` lookupInEnv name ds
lookupInEnv name []     = mzero

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
  { varIDSupply :: !(IdentSupply Var)
  , currentModule :: !ModuleName
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
    (x, _, errs) <- runNR m env (Map.empty : names)
    return (x, names, errs)

-- | Define a variable.  The variable is added to the current scope,
--   and can be looked up with 'use'.
def :: Identifier Parsed -> Identifier Resolved -> NR ()
def parsed_name resolved_var =
  NR $ \env names ->
    let s = addToEnv parsed_name resolved_var names
    in returnNR () s

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

-------------------------------------------------------------------------------
-- Name resolution

resolveL :: (SourcePos -> a -> NR b) -> Located a -> NR (Located b)
resolveL f (L pos x) = L pos <$> f pos x

-- | Create and define a new variable inhabiting the current module.
newRVar :: Level -> Identifier Parsed -> NR ResolvedVar
newRVar lv parsed_name = do
  modname <- getModuleName
  id <- fresh
  let label = plainLabel modname parsed_name
      v = ResolvedVar (mkVar id (Just label) lv)
  def parsed_name v
  return v

resolveLType (L pos t) = do
  (t', lv) <- resolveType pos t 
  return (L pos t', lv)

-- | Resolve a type expression.  Return the type and the inferred level.
--   The level is used for error checking.
resolveType :: SourcePos -> PType -> NR (RType, Level)
resolveType pos ty =
  case ty
  of VarT v      -> do v' <- use v pos
                       check_level (getLevel v')
                       return (VarT v', getLevel v')
     IntIndexT n -> return (IntIndexT n, TypeLevel)
     TupleT ts -> do (args, arg_lvs) <- mapAndUnzipM resolveLType ts
                     logErrorIf (any (TypeLevel /=) arg_lvs) $
                       "Arguments of tuple type must be types"
                     return (TupleT args, TypeLevel)
     AppT op arg -> do (op', op_lv) <- resolveLType op
                       (arg', _) <- resolveLType arg
                       return (AppT op' arg', op_lv)
     FunT d r    -> do (d', d_lv) <- resolveLType d
                       (r', r_lv) <- resolveLType r
                       logErrorIf (d_lv /= r_lv) $
                         "Domain and range of function type must have same level"
                       return (FunT d' r', r_lv)
     AllT d r    -> fmap fst $ resolveDomain d $ \d' -> do
                      (r', lv) <- resolveLType r
                      return (AllT d' r', lv)
     LamT d r    -> withMany (resolveDomainT pos) d $ \d' -> do
                      (r', lv) <- resolveLType r
                      return (LamT d' r', lv)
     CoT k d r   -> do (k', k_lv) <- resolveLType k
                       (d', d_lv) <- resolveLType d
                       (r', r_lv) <- resolveLType r
                       logErrorIf (k_lv /= KindLevel) $
                         "First argument of coercion type must be a kind"
                       logErrorIf (d_lv /= TypeLevel || r_lv /= TypeLevel) $
                         "Arguments to coercion type must have same level"
                       return (CoT k' d' r', TypeLevel)
  where
    check_level lv =
      logErrorIf (lv == ObjectLevel) $
      "Term must be higher than Object level (" ++ show pos ++ ")"

-- | Resolve a variable binding.  Return the level of the variable's type.
resolveDomain :: Domain Parsed -> (Domain Resolved -> NR a) -> NR (a, Level)
resolveDomain (Domain binder t) k = do
  (t', lv) <- resolveLType t
  x <- enter $ do binder' <- newRVar (pred lv) binder
                  k (Domain binder' t')
  return (x, lv)

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

resolveDomainT = resolveDomain' KindLevel 
                 "Bad level in type parameter of data constructor"

resolveDomainV = resolveDomain' TypeLevel
                 "Bad level in field of data constructor" 

resolveExp :: SourcePos -> Exp Parsed -> NR (Exp Resolved)
resolveExp pos expression = 
  case expression
  of VarE v -> VarE <$> use v pos
     IntE n -> pure $ IntE n
     FloatE n -> pure $ FloatE n
     TupleE ts -> TupleE <$> mapM (resolveL resolveExp) ts
     TAppE e t -> do
       e' <- resolveL resolveExp e 
       (t', t_lv) <- resolveLType t
       logErrorIf (t_lv /= TypeLevel) $
         "Parameter of type application is not a type (" ++ show pos ++ ")"
       return $ TAppE e' t'
     AppE e1 e2 -> AppE <$> resolveL resolveExp e1 <*> resolveL resolveExp e2
     LamE f -> LamE <$> resolveFun pos f
     LetE binder rhs body -> do
       rhs' <- resolveL resolveExp rhs
       resolveDomain' TypeLevel "Bad level in let binding" pos binder $ \binder' -> do
         body' <- resolveL resolveExp body
         return $ LetE binder' rhs' body'
     LetTypeE lhs rhs body -> do
       (rhs', rhs_lv) <- resolveLType rhs 
       logErrorIf (rhs_lv == ObjectLevel) $
         "Bad level in right-hand side of type let"
       enter $ do lhs' <- newRVar rhs_lv lhs
                  body' <- resolveL resolveExp body
                  return $ LetTypeE lhs' rhs' body'
     LetfunE defs e ->
       resolveDefGroup defs $ \defs' -> LetfunE defs' <$> resolveL resolveExp e
     CaseE scr alts -> CaseE <$> resolveL resolveExp scr <*>
                       mapM (resolveL resolveAlt) alts
     ExceptE t -> do
       (t', t_lv) <- resolveLType t
       logErrorIf (t_lv /= TypeLevel) $
         "Result type of exception is not a type"
       return $ ExceptE t'
     
     CoerceE from_t to_t body -> do
       (from_t', from_t_lv) <- resolveLType from_t
       (to_t', to_t_lv) <- resolveLType to_t
       logErrorIf (from_t_lv /= TypeLevel) $
         "Source type of coercion is not a type"
       logErrorIf (to_t_lv /= TypeLevel) $
         "Result type of coercion is not a type"
       body' <- resolveL resolveExp body
       return $ CoerceE from_t' to_t' body'

resolveDefGroup :: [LDef Parsed] -> ([LDef Resolved] -> NR a) -> NR a
resolveDefGroup defs k = enter $ do
  -- Create a new variable for each local variable
  let variables = map (dName . unLoc) defs
  resolved <- mapM (newRVar ObjectLevel) variables
  
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

resolvePattern pos (ConPattern con ty_args ex_types fields) k = do
  con' <- use con pos
  (ty_args', ty_lvs) <- mapAndUnzipM resolveLType ty_args
  logErrorIf (any (TypeLevel /=) ty_lvs) $
    "Type parameter is not a type (" ++ show pos ++ ")"
  withMany (resolveDomainT pos) ex_types $ \ex_types' ->
    withMany (resolveDomainV pos) fields $ \fields' ->
    k (ConPattern con' ty_args' ex_types' fields')

resolvePattern pos (TuplePattern fields) k =
    withMany (resolveDomainV pos) fields $ \fields' ->
    k (TuplePattern fields')

resolveFun :: SourcePos -> PFun -> NR RFun
resolveFun pos f =
  withMany (resolveDomainT pos) (fTyParams f) $ \tparams ->
  withMany (resolveDomainV pos) (fParams f) $ \params -> do
    (range, range_lv) <- resolveLType $ fRange f
    logErrorIf (range_lv /= TypeLevel) $
      "Function range is not a type"
    body <- resolveL resolveExp $ fBody f
    return $ Fun tparams params range body  

resolveDataConDecl :: SourcePos
                   -> ResolvedVar -- ^ The resolved data constructor
                   -> DataConDecl Parsed
                   -> NR (DataConDecl Resolved)
resolveDataConDecl pos v' (DataConDecl _ ty_params ex_types args) = do
  enter $
    withMany (resolveDomainT pos) ty_params $ \ty_params' ->
    withMany (resolveDomainT pos) ex_types $ \ex_types' -> do
      (unzip -> (args', arg_levels)) <- mapM resolveLType args
      mapM_ check_arg_level arg_levels
      return $ DataConDecl v' ty_params' ex_types' args'
  where
    check_arg_level lv =
      logErrorIf (lv /= TypeLevel) $
      "Bad level in field of data constructor (" ++ show pos ++ ")"

    check_rng_level lv =
      logErrorIf (lv /= TypeLevel) $
      "Bad level in range of data constructor (" ++ show pos ++ ")"

resolveEntity :: ResolvedDeclName -> Entity Parsed -> NR (Entity Resolved)
resolveEntity _ (VarEnt ty attrs) = do
  (ty', lv) <- resolveLType ty
  logErrorIf (lv /= TypeLevel) $
    "Expecting a type (" ++ show (getSourcePos ty) ++ ")"
  return $ VarEnt ty' attrs

resolveEntity (GlobalName r_name) (TypeEnt ty) = do
  (ty', lv) <- resolveLType ty
  logErrorIf (lv /= KindLevel) $
    "Expecting a kind (" ++ show (getSourcePos ty) ++ ")"
  return $ TypeEnt ty'

resolveEntity (DataConNames _ data_con_names) (DataEnt ty cons attrs) = do
  (ty', lv) <- resolveLType ty
  logErrorIf (lv /= KindLevel) $
    "Expecting a kind (" ++ show (getSourcePos ty) ++ ")"
  cons' <- sequence [L pos <$> resolveDataConDecl pos v con
                    | (v, L pos con) <- zip data_con_names cons]
  return $ DataEnt ty' cons' attrs

resolveEntity _ (ConstEnt ty e attrs) = do
  (ty', lv) <- resolveLType ty
  logErrorIf (lv /= TypeLevel) $
    "Expecting a type (" ++ show (getSourcePos ty) ++ ")"
  e' <- resolveL resolveExp e
  return $ ConstEnt ty' e' attrs

resolveEntity _ (FunEnt f attrs) = do
  f' <- resolveL resolveFun f
  return $ FunEnt f' attrs

-- | Resolve a global declaration.  The declared variable should be in the
--   environment already.
resolveDecl :: ResolvedDeclName -> PLDecl -> NR RLDecl
resolveDecl r_name (L pos (Decl _ ent)) = do
  r_ent <- resolveEntity r_name ent
  return $ L pos (Decl (resolvedGlobal r_name) r_ent)

data ResolvedDeclName =
    GlobalName {resolvedGlobal :: ResolvedVar}
  | DataConNames {resolvedGlobal :: ResolvedVar,
                  resolvedDataConstructors :: [ResolvedVar]}

resolveDeclName (L _ (Decl name ent)) =
  case ent
  of VarEnt {}                -> object_level
     TypeEnt {}               -> type_level
     DataEnt _ constructors _ -> data_definition constructors
     ConstEnt {}              -> object_level
     FunEnt {}                -> object_level
  where
    object_level = liftM GlobalName $ newRVar ObjectLevel name
    type_level = liftM GlobalName $ newRVar TypeLevel name
    data_definition constructors = do
      tycon <- newRVar TypeLevel name
      datacons <- sequence [newRVar ObjectLevel $ dconVar d
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

resolveModule :: IdentSupply Var -- ^ Supply of unique variable IDs
              -> Map.Map (Identifier Parsed) ResolvedVar
              -> ModuleName     -- ^ Name of module being processed
              -> PModule       -- ^ The parsed module
              -> IO RModule
resolveModule id_supply predef modname mod = do
  let init_environment = Environment id_supply modname
      init_env = [predef]
  (mod', env, errors) <- runNR (resolveModule' mod) init_environment init_env
  case getErrors errors of
    [] -> case mod' of Just m -> return m
    es -> do mapM_ putStrLn es
             fail "Name resolution failed"
