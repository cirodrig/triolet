{-| Resolve names
-}

{-# LANGUAGE FlexibleInstances #-}
module CParser.Resolve(globalEnvironment, resolveModule)
where

import Control.Monad
import qualified Data.Map as Map
import Data.Maybe

import Common.Identifier
import Common.Supply
import Common.SourcePos
import Common.Label
import Type.Var
import CParser.AST

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
addToEnv parsed_name resolved_var (d:ds) = Map.insert parsed_name resolved_var d : ds

addToEnv _ _ [] = error "addToEnv: Empty environment"


-- | Search for a name in the environment
lookupInEnv :: Identifier Parsed -> Env -> Maybe (Identifier Resolved)
lookupInEnv name (d:ds) = Map.lookup name d `mplus` lookupInEnv name ds
lookupInEnv name []     = mzero

lookupInTopEnv :: Identifier Parsed -> Env -> Maybe (Identifier Resolved)
lookupInTopEnv name (d:ds) = Map.lookup name d
lookupInTopEnv name []     = mzero

lookupInDefEnv :: Identifier Parsed -> Env -> Maybe (Identifier Resolved)
lookupInDefEnv name (d:[]) = Map.lookup name d
lookupInDefEnv name (d:ds) = lookupInDefEnv name ds
lookupInDefEnv name []     = mzero

{-
-- | The initial environment, as seen when name resolution starts.
--
-- TODO: Add predefined variables such as 'Pure' to this environment.
globalEnv :: Env
globalEnv = [Map.empty]

predefinedVars :: [Identifier Parsed]
predefinedVars = ["int", "float", "bool"] ++ ["list", "iter"] ++ ["Pure", "Effect"] ++ ["NoneType", "LazyStream", "Stream", "Array"] ++ ["@", "**"] ++ ["PassConv", "EqDict", "OrdDict", "AdditiveDict", "TraversableDict", "PyonTuple2"] ++ ["Unfound Error"]


addUnfoundError = do
  let s = "Unfound Error"
  errVar <-  builtInVar s
  def s errVar
  
  -}

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
newtype NR a = NR {runNR :: Environment -> Env -> IO (a, Env, Errors)}

returnNR x e = return (x, e, noErrors)

instance Monad NR where
  return x = NR (\_ e -> returnNR x e)
  m >>= k = NR (\env names -> do (x, e1, errs1) <- runNR m env names
                                 (y, e2, errs2) <- runNR (k x) env e1
                                 return (y, e2, errs1 . errs2))

instance Supplies NR (Ident Var) where
  fresh = NR (\env e -> do
    s <- supplyValue (varIDSupply env)
    returnNR s e)
  supplyToST = undefined -- Raises warning if not provided

-- | Get the current module's name.
getModuleName :: NR ModuleName
getModuleName = NR (\env e -> returnNR (currentModule env) e)

-- | Log an error if a 'Just' value is given, otherwise do nothing.
--   Execution continues normally after the error is logged.
logErrorMaybe :: Maybe Error -> NR ()
logErrorMaybe merr = NR (\_ e -> return ((), e, maybeError merr))

-- | Log an error.
--   This doesn't interrupt execution; execution continues normally
--   after the error is logged.
logError :: Error -> NR ()
logError err = NR (\_ e -> return ((), e, (err:)))


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

-- | \"Define\" a global variable.  We actually look up a predefined variable 
--   name here, like 'use', but with a different error message.
globalDef :: Identifier Parsed -> SourcePos -> NR (Identifier Resolved)
globalDef = fetch "Could not find global name:"

use :: Identifier Parsed -> SourcePos -> NR (Identifier Resolved)
use = fetch "Could not find:"

-- | Use a variable, but provide location information in case of an error
fetch :: String -> Identifier Parsed -> SourcePos -> NR (Identifier Resolved)
fetch error_header parsed_name pos = NR $ \env names ->
  let m_ident = lookupInEnv parsed_name names
      error_message = if isNothing m_ident then Just not_found else Nothing
      Just i = m_ident
  in return (i, names, (maybeToList error_message ++))
  where
    not_found = error_header ++ " " ++ parsed_name ++ " (" ++ show pos ++ ")"

-------------------------------------------------------------------------------
-- Name resolution

{-
builtInVar :: Identifier Parsed -> NR ResolvedVar
builtInVar parsed_name = do
  id <- fresh
  return $ ResolvedVar id (Just $ builtinLabel parsed_name) Nothing
-}

-- | Create a new variable inhabiting the current module.
newRVar :: Identifier Parsed -> NR ResolvedVar
newRVar parsed_name = do
  modname <- getModuleName
  id <- fresh
  return $ ResolvedVar id (Just $ pyonLabel modname parsed_name) Nothing
  
ckVar :: Identifier Parsed -> NR (Maybe ResolvedVar)
ckVar parsed_name = NR $ \env names -> 
  case (lookupInDefEnv parsed_name names) of
    Just i -> return ( Just i, names, maybeError $ Just ("Conflict newly defining: "++parsed_name++". Name already exists in default environment"))
    Nothing -> return (Nothing, names, noErrors)
  

-- | Convenience routine to make a new variable and define it
mkdfVar :: Identifier Parsed -> NR ResolvedVar
mkdfVar parsed_name = do
      ck <- ckVar parsed_name
      case ck of
        Just i -> return i
        Nothing -> do
          resolved <- newRVar parsed_name
          def parsed_name resolved
          return resolved


resolveModuleNR :: PModule -> NR RModule
resolveModuleNR (Module dlist) = do
  rlist <- enter $ mapM resolveDecl dlist
  return $ Module rlist

resolveDataConDecl (L pos (DataConDecl v ty params ex_types args rng)) = do
  rVar <- globalDef v pos
  rType <- enter $ resolveReturnType ty
  enter $ do
    rParams <- mapM resolveParamType params
    (rExTypes, rArgs) <- enter $ do
      rExTypes <- mapM resolveParamType ex_types
      rArgs <- mapM resolveReturnType args
      return (rExTypes, rArgs)
    -- The return type may not mention existential variables
    rRng <- resolveReturnType rng
    return $ L pos $ DataConDecl rVar rType rParams rExTypes rArgs rRng

resolveDecl :: (Located (Decl Parsed)) -> NR (Located (Decl Resolved))
resolveDecl (L pos decl) =
  case decl
  of VarDecl v ty -> do
       rVar <- globalDef v pos
       rType <- enter $ resolveReturnType ty
       return $ L pos $ VarDecl rVar rType
     DataDecl v repr ty cons -> do
       rVar <- globalDef v pos
       rType <- enter $ resolveReturnType ty
       rCons <- mapM resolveDataConDecl cons
       return $ L pos $ DataDecl rVar repr rType rCons

resolveLType :: PLType -> NR RLType
resolveLType (L pos lt) =
  case lt of
    VarT tVar -> do rVar <- use tVar pos
                    return $ L pos (VarT rVar)
    AppT tOper tArgs -> do oper <- resolveLType tOper
                           args <- mapM resolveLType tArgs
                           return $ L pos (AppT oper args)
    FunT fParam fRng -> do rFun <- enter $ resolveFun lt
                           return $ L pos rFun
                        
resolveFun :: PType -> NR RType
resolveFun (FunT fParam fRng) =  do 
  rParam <- resolveParamType fParam
  rRng <- resolveReturnType fRng
  return $ FunT rParam rRng

resolveParamType :: (ParamType Parsed) -> NR (ParamType Resolved)
resolveParamType (ParamType repr ty) = do
  ty' <- resolveLType ty
  repr' <- case repr
           of ValuePT (Just v) -> liftM (ValuePT . Just) $ mkdfVar v
              ValuePT Nothing -> return (ValuePT Nothing)
              BoxedPT -> return BoxedPT
              ReadPT -> return ReadPT
              WritePT -> return WritePT
  return $ ParamType repr' ty'

resolveReturnType :: (ReturnType Parsed) -> NR (ReturnType Resolved)
resolveReturnType (ReturnType pRepr pType) = do
  rType <- resolveLType pType
  return $ ReturnType pRepr rType

globalEnvironment :: IdentSupply Var
                  -> [(String, VarDetails)]
                  -> IO (Map.Map (Identifier Parsed) ResolvedVar)
globalEnvironment supply xs = liftM Map.fromList $ mapM mk_var xs
  where
    mk_var (name, details) = do
      var_id <- supplyValue supply
      return (name, ResolvedVar var_id Nothing (Just details))

resolveModule :: IdentSupply Var -- ^ Supply of unique variable IDs
              -> Map.Map (Identifier Parsed) ResolvedVar
              -> ModuleName     -- ^ Name of module being processed
              -> PModule       -- ^ The parsed module
              -> IO RModule
resolveModule id_supply predef modname mod = do
  let init_environment = Environment id_supply modname
      init_env = [predef]
  (mod', env, errors) <- runNR (resolveModuleNR mod) init_environment init_env
  case getErrors errors of
    [] -> return mod'
    es -> do mapM_ putStrLn es
             fail "Name resolution failed"
