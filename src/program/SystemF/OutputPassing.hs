{-| This module uses the annotated program from representation inference 
to insert explicit data movement code.
This includes loading values, storing values, and passing \"output pointers\"
to functions.
-}

{-# LANGUAGE FlexibleInstances #-}
module SystemF.OutputPassing (generateMemoryIR)
where

import Prelude hiding(mapM)
import Control.Monad hiding(mapM)
import Control.Monad.Trans
import Data.Traversable(mapM)
  
import Common.Error
import Common.Identifier
import Common.Supply
  
import Builtins.Builtins
import qualified SystemF.DictEnv as DictEnv
import SystemF.ReprDict
import SystemF.EtaReduce
import SystemF.Syntax
import SystemF.Typecheck
import SystemF.Representation
import SystemF.MemoryIR
import Type.Environment
import Type.Rename
import Type.Type
import GlobalVar
import Globals

loadOp = ExpM $ VarE defaultExpInfo (pyonBuiltin the_load)
storeOp = ExpM $ VarE defaultExpInfo (pyonBuiltin the_store)
copyOp = ExpM $ VarE defaultExpInfo (pyonBuiltin the_copy)

loadBoxOp = ExpM $ VarE defaultExpInfo (pyonBuiltin the_loadBox)
storeBoxOp = ExpM $ VarE defaultExpInfo (pyonBuiltin the_storeBox)
boxToPtrOp = ExpM $ VarE defaultExpInfo (pyonBuiltin the_boxToPtr)
ptrToBoxOp = ExpM $ VarE defaultExpInfo (pyonBuiltin the_ptrToBox)

returnApp op ty_args args =
  return $ ExpM $ AppE defaultExpInfo op ty_args args

-- | Keep track of global variables and representation dictionaries
data OPEnv = OPEnv { opVarSupply :: {-# UNPACK #-}!(IdentSupply Var)
                     
                   , opTypeEnv :: TypeEnv
                     
                     -- Representation dictionaries, indexed by the
                     -- dictionary's parameter type
                   , opDictEnv :: MkDictEnv
                   , opIntEnv :: IntIndexEnv
                   }

newtype OP a = OP {runOP :: OPEnv -> Maybe ExpM -> IO a}

instance Monad OP where
  return x = OP (\_ _ -> return x)
  m >>= k = OP $ \env ret_arg -> do
    x <- runOP m env ret_arg
    runOP (k x) env ret_arg

instance Supplies OP (Ident Var) where
  fresh = OP $ \env _ -> supplyValue (opVarSupply env)

instance MonadIO OP where
  liftIO m = OP (\_ _ -> m)

instance ReprDictMonad OP where
  withVarIDs f = OP $ \env mrarg -> runOP (f $ opVarSupply env) env mrarg
  withTypeEnv f = OP $ \env mrarg -> runOP (f $ opTypeEnv env) env mrarg
  withDictEnv f = OP $ \env mrarg -> runOP (f $ opDictEnv env) env mrarg
  getIntIndexEnv = OP $ \env _ -> return (opIntEnv env)
  localDictEnv f m = OP $ \env rarg ->
    let env' = env {opDictEnv = f $ opDictEnv env}
    in runOP m env' rarg
  localIntIndexEnv f m = OP $ \env rarg ->
    let env' = env {opIntEnv = f $ opIntEnv env}
    in runOP m env' rarg

-- | Get the current return argument, and reset it.
takeRetArg :: (ExpM -> OP a) -> OP a
takeRetArg k = OP $ \env mrarg ->
  case mrarg
  of Nothing -> internalError "takeRetArg"
     Just rarg -> runOP (k rarg) env Nothing

-- | Set the return argument for some code.
withRetArg :: ExpM -> OP a -> OP a
withRetArg ra k = OP $ \env _ -> runOP k env (Just ra)

-------------------------------------------------------------------------------
-- Initial value of environment
    
-- | Set up the global environment for creating memory IR
setupEnvironment :: IdentSupply Var -> IO OPEnv
setupEnvironment var_supply = do
  type_env <- readInitGlobalVarIO the_newCoreTypes
  (dict_env, int_env) <- runFreshVarM var_supply createDictEnv
  return (OPEnv var_supply type_env dict_env int_env)

-------------------------------------------------------------------------------
-- Transformations on IR data structures

genExp :: Exp Rep -> OP ExpM
genExp expression =
  case expression
  of LoadExpr Value ty e ->
       withReprDict ty $ \repr_dict -> do
         e' <- genExp e
         returnApp loadOp [TypM ty] [repr_dict, e']
     LoadExpr Boxed ty e -> do
       e' <- genExp e
       returnApp loadBoxOp [TypM ty] [e']
     StoreExpr Value ty e ->
       takeRetArg $ \ret_arg ->
       withReprDict ty $ \repr_dict -> do
         e' <- genExp e
         returnApp storeOp [TypM ty] [repr_dict, e', ret_arg]
     StoreExpr Boxed ty e ->
       takeRetArg $ \ret_arg -> do
         e' <- genExp e
         returnApp storeBoxOp [TypM ty] [e', ret_arg]
     AsBoxExpr ty e -> do
       e' <- genExp e
       returnApp ptrToBoxOp [TypM ty] [e']
     AsReadExpr ty e -> do
       e' <- genExp e
       returnApp boxToPtrOp [TypM ty] [e']
     CopyExpr ty e -> do
       e' <- genExp e
       takeRetArg $ \ret_arg ->
         withReprDict ty $ \repr_dict -> do
           returnApp copyOp [TypM ty] [repr_dict, e', ret_arg]
     ExpR rt e -> genExp' rt e

genExp' :: ReturnType -> BaseExp Rep -> OP ExpM
genExp' return_type expression =
  case expression
  of VarE inf v ->
       let var_expr = ExpM $ VarE inf v
       in case return_type
          of WriteRT ::: ty ->
               -- Apply this variable to the return argument
               takeRetArg $ \ret_arg ->
               return $ ExpM $ AppE inf var_expr [] [ret_arg]
             _ -> return var_expr
     LitE inf l ->
       -- Return arguments are not possible here
       return $ ExpM $ LitE inf l
     AppE inf op ty_args args -> maybe_take_ret_arg $ \ret_arg -> do
       op' <- genExp op
       let ty_args' = [TypM t | TypR t <- ty_args]
       args' <- mapM genArgument args
       return $ ExpM $ AppE inf op' ty_args' (args' ++ ret_arg)
     LamE inf f -> do
       f' <- genFun f
       return $ ExpM $ LamE inf f'
     LetE inf lhs rhs body ->
       genLet inf lhs rhs body
     LetfunE inf defs body -> do
       defs' <- mapM genDef defs
       body' <- genExp body
       return $ ExpM $ LetfunE inf defs' body'
     CaseE inf scr alts -> do
       scr' <- genExp scr
       alts' <- mapM genAlt alts
       return $ ExpM $ CaseE inf scr' alts'
  where
    -- Take the return argument, if appropriate, and pass it as a list to
    -- the continuation
    maybe_take_ret_arg k =
      case return_type
      of WriteRT ::: ty -> takeRetArg (\ra -> k [ra])
         _ -> k []

-- | Generate a let expression.
genLet inf (PatR pat_var pat_type) rhs body =
  case pat_type
  of WritePT ::: ty ->
       -- This pattern binds a locally allocated variable
       let mem_ty = convertToMemType ty
       in withReprDict mem_ty $ \repr_dict -> do
         let pattern = localVarP pat_var mem_ty repr_dict
             ret_arg = ExpM $ VarE defaultExpInfo pat_var
         rhs' <- withRetArg ret_arg $ genExp rhs
         body' <- genExp body
         return $ ExpM $ LetE inf pattern rhs' body'

     OutPT ::: _ -> internalError "genLet"
     SideEffectPT ::: _ -> internalError "genLet"

     _ -> do
       -- This pattern binds a scalar variable
       let pattern = memVarP pat_var (convertToMemParamType pat_type)
       rhs' <- genExp rhs
       body' <- genExp body
       return $ ExpM $ LetE inf pattern rhs' body'

-- | Generate an expression that appears as an argument to something 
--   such as a function.
--
--   If an argument returns by writing, we create a lambda function so that 
--   the argument's output variable can be found.
--   Other arguments are generated normally.
genArgument :: ExpR -> OP ExpM
genArgument expression =
  case returnType expression
  of WriteRT ::: ty -> do
       tmpvar <- newAnonymousVar ObjectLevel
       let argexp = ExpM $ VarE defaultExpInfo tmpvar
       lam_body <- withRetArg argexp $ genExp expression
       
       -- Create the lambda function
       let function =
             FunM $ Fun { funInfo = defaultExpInfo
                        , funTyParams = []
                        , funParams = [memVarP tmpvar (OutPT ::: ty)]
                        , funReturn = RetM (SideEffectRT ::: ty)
                        , funBody = lam_body}
       return $ ExpM $ LamE defaultExpInfo function

     _ -> genExp expression

genFun :: FunR -> OP FunM
genFun (FunR f) = do
  (return_var, return_pat, return_ret) <- mk_return_pat (funReturn f)
  let ty_pats = [TyPatM v t | TyPatR v t <- funTyParams f]
      pats = map mk_pat (funParams f) ++ return_pat
  
  body <- with_return_var return_var $
          saveReprDictPatterns pats $
          genExp (funBody f)
  return $ FunM $ Fun { funInfo = funInfo f
                      , funTyParams = ty_pats
                      , funParams = pats
                      , funReturn = return_ret
                      , funBody = body}
  where
    mk_pat (PatR v pat_type) =
      let new_pat_type = convertToMemParamType pat_type
      in memVarP v new_pat_type

    -- Create the return parameter if one is needed
    mk_return_pat (RetR (WriteRT ::: ty)) = do
      return_var <- newAnonymousVar ObjectLevel
      return (Just return_var,
              [memVarP return_var (OutPT ::: ty)],
              RetM (SideEffectRT ::: ty))
    
    mk_return_pat (RetR return_type) =
      return (Nothing, [], RetM return_type)

    with_return_var Nothing m = m
    with_return_var (Just rv) m =
      let ret_arg = ExpM $ VarE defaultExpInfo rv
      in withRetArg ret_arg m

genAlt :: Alt Rep -> OP (Alt Mem)
genAlt (AltR alt) = do
  let ty_args = [TypM t | TypR t <- altTyArgs alt]
      ex_types = [TyPatM v t | TyPatR v t <- altExTypes alt]
      params = map mk_pat $ altParams alt
  body <- genExp $ altBody alt
  return $ AltM $ Alt { altConstructor = altConstructor alt
                      , altTyArgs = ty_args
                      , altExTypes = ex_types
                      , altParams = params
                      , altBody = body}
  where
    mk_pat (PatR v (repr ::: ty)) =
      let new_repr =
            case repr
            of ValPT Nothing -> ValPT Nothing
               BoxPT -> BoxPT
               ReadPT -> ReadPT
               _ -> internalError "genAlt"
      in memVarP v (new_repr ::: convertToMemType ty)

genDef :: Def Rep -> OP (Def Mem)
genDef (Def v f) = do
  f' <- genFun f
  return (Def v f')

genExport :: Export Rep -> OP (Export Mem)
genExport (Export pos spec f) = do
  f' <- genFun f
  return (Export pos spec f')

genModule :: Module Rep -> OP (Module Mem)
genModule (Module mod_name defss exports) = do
  defss' <- mapM (mapM genDef) defss
  exports' <- mapM genExport exports
  return $ Module mod_name defss' exports'

generateMemoryIR :: Module (Typed SF) -> IO (Module Mem)
generateMemoryIR mod = do
  repr_mod <- inferRepresentations mod

  mem_mod <- withTheNewVarIdentSupply $ \var_supply -> do
    global_env <- setupEnvironment var_supply
    runOP (genModule repr_mod) global_env Nothing

  -- Eta-reduction is disabled. 
  -- It's not always a valid transformation because it changes side effects,
  -- sometimes resulting in dangling pointer accesses.
  -- Do we still need it?

  -- return $ etaReduceModule mem_mod
  return mem_mod
