{-| This module uses the annotated program from representation inference 
to insert explicit data movement code.
This includes loading values, storing values, and passing \"output pointers\"
to functions.
-}

{-# LANGUAGE FlexibleInstances #-}
module SystemF.OutputPassing (generateMemoryIR)
where

import Common.Error
import Common.Identifier
import Common.Supply
  
import Builtins.Builtins
import qualified SystemF.DictEnv as DictEnv
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

-- | Given a substitution, construct a dictionary and make the dictionary
--   available over the scope of some computation.
type MkDict = (ExpM -> OP ExpM) -> OP ExpM

-- | Keep track of global variables and representation dictionaries
data OPEnv = OPEnv { opVarSupply :: {-# UNPACK #-}!(IdentSupply Var)
                     
                   , opTypeEnv :: TypeEnv
                     
                     -- Representation dictionaries, indexed by the
                     -- dictionary's parameter type
                   , opDictEnv :: DictEnv.DictEnv MkDict
                   }

newtype OP a = OP {runOP :: OPEnv -> Maybe ExpM -> IO a}

instance Monad OP where
  return x = OP (\_ _ -> return x)
  m >>= k = OP $ \env ret_arg -> do
    x <- runOP m env ret_arg
    runOP (k x) env ret_arg

instance Supplies OP (Ident Var) where
  fresh = OP $ \env _ -> supplyValue (opVarSupply env)

-- | Get the current return argument, and reset it.
takeRetArg :: (ExpM -> OP a) -> OP a
takeRetArg k = OP $ \env mrarg ->
  case mrarg
  of Nothing -> internalError "takeRetArg"
     Just rarg -> runOP (k rarg) env Nothing

-- | Set the return argument for some code.
withRetArg :: ExpM -> OP a -> OP a
withRetArg ra k = OP $ \env _ -> runOP k env (Just ra)

lookupDictionary :: Type -> OP (Maybe MkDict)
lookupDictionary ty = OP $ \env _ ->
  case ty
  of FunT {} ->
       -- Functions all have the same representation
       return $ Just $ mk_fun_dict ty
     _ -> DictEnv.lookup (opVarSupply env) (opTypeEnv env) ty (opDictEnv env)
  where
    mk_fun_dict ty k =
      -- Create a boxed representation object, and pass it to the continuation 
      let op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_Boxed)
          call = ExpM $ AppE defaultExpInfo op [TypM ty] []
      in k call

-- | Add a dictionary to the environment.  It will be used if it is 
--   needed in the remainder of the computation.
saveDictionary :: Type -> ExpM -> OP a -> OP a
saveDictionary dict_type dict_exp k = OP $ \env mrarg -> do
  let dict_pattern = DictEnv.monoPattern dict_type ($ dict_exp)
      env' = env {opDictEnv = DictEnv.insert dict_pattern $ opDictEnv env}
    in runOP k env' mrarg

withReprDictionary :: Type -> (ExpM -> OP ExpM) -> OP ExpM
withReprDictionary param_type f = do
  mdict <- lookupDictionary param_type
  case mdict of
    Just dict -> do dict f
    Nothing -> internalError $ "withReprDictionary: Cannot construct dictionary for type:\n" ++ show (pprType param_type)

-- | If the pattern binds a representation dictionary, record the dictionary 
--   in the environment so it can be looked up later.
saveDictionaryPattern :: PatM -> OP a -> OP a
saveDictionaryPattern pattern m = 
  case pattern
  of MemVarP pat_var (ReadPT ::: ty)
       | Just repr_type <- get_repr_type ty ->
           saveDictionary repr_type (ExpM $ VarE defaultExpInfo pat_var) m
     _ -> m
  where
    get_repr_type ty = 
      case fromVarApp ty 
      of Just (op, [arg])
           | op `isPyonBuiltin` the_Repr -> Just arg
         _ -> Nothing

-- | Find patterns that bind representation dictionaries, and record them
--   in the environment.
saveDictionaryPatterns :: [PatM] -> OP a -> OP a
saveDictionaryPatterns ps m = foldr saveDictionaryPattern m ps

-------------------------------------------------------------------------------
-- Initial value of environment
    
-- | Set up the global environment for creating memory IR
setupEnvironment :: IdentSupply Var -> IO OPEnv
setupEnvironment var_supply = do
  type_env <- readInitGlobalVarIO the_newCoreTypes
  dict_env <- runFreshVarM var_supply createDictEnv
  return (OPEnv var_supply type_env dict_env)

createDictEnv :: FreshVarM (DictEnv.DictEnv MkDict)
createDictEnv = do
  let int_dict = DictEnv.monoPattern (VarT (pyonBuiltin the_int))
                 ($ ExpM $ VarE defaultExpInfo $ pyonBuiltin the_repr_int)
  let float_dict = DictEnv.monoPattern (VarT (pyonBuiltin the_float))
                   ($ ExpM $ VarE defaultExpInfo $ pyonBuiltin the_repr_float)
  repr_dict <- DictEnv.pattern1 $ \arg ->
    (varApp (pyonBuiltin the_Repr) [VarT arg],
     createDict_Repr arg)
  tuple2_dict <- DictEnv.pattern2 $ \arg1 arg2 ->
    (varApp (pyonBuiltin the_PyonTuple2) [VarT arg1, VarT arg2],
     createDict_Tuple2 arg1 arg2)
  additive_dict <- DictEnv.pattern1 $ \arg ->
    (varApp (pyonBuiltin the_AdditiveDict) [VarT arg],
     createSimpleDict the_AdditiveDict the_repr_AdditiveDict arg)
  multiplicative_dict <- DictEnv.pattern1 $ \arg ->
    (varApp (pyonBuiltin the_MultiplicativeDict) [VarT arg],
     createSimpleDict the_MultiplicativeDict the_repr_MultiplicativeDict arg)
  return $ DictEnv.DictEnv [repr_dict,
                            float_dict, int_dict,
                            tuple2_dict, additive_dict, multiplicative_dict]

getParamType v subst =
  case substituteVar v subst
  of Just v -> v
     Nothing -> internalError "getParamType"

-- | Add a dictionary to the environment and pass it to the given computation.
saveAndUseDict :: Type -> ExpM -> (ExpM -> OP ExpM) -> OP ExpM
saveAndUseDict dict_type dict_val k =
  saveDictionary dict_type dict_val $ k dict_val

createDict_Tuple2 param_var1 param_var2 subst use_dict =
  withReprDictionary param1 $ \dict1 ->
  withReprDictionary param2 $ \dict2 ->
  withReprDictionary dict_type $ \dict_repr -> do
    tmpvar <- newAnonymousVar ObjectLevel
    let dict_exp = ExpM $ VarE defaultExpInfo tmpvar
    body <- saveAndUseDict data_type dict_exp use_dict
    return $ ExpM $ LetE { expInfo = defaultExpInfo 
                         , expBinder = mk_pat tmpvar dict_repr
                         , expValue = mk_dict tmpvar dict1 dict2
                         , expBody = body}
  where
    param1 = getParamType param_var1 subst
    param2 = getParamType param_var2 subst
    
    data_type = varApp (pyonBuiltin the_PyonTuple2) [param1, param2]
    dict_type = varApp (pyonBuiltin the_Repr) [data_type]
    
    -- Construct the local variable pattern
    mk_pat tmpvar dict_repr =
      LocalVarP tmpvar dict_type dict_repr
    
    -- Construct the dictionary
    mk_dict tmpvar dict1 dict2 =
      let oper = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_PyonTuple2)
          return_arg = ExpM $ VarE defaultExpInfo tmpvar
      in ExpM $ AppE defaultExpInfo oper [TypM param1, TypM param2]
         [dict1, dict2, return_arg]

-- | Representation of 'Repr' dictionaries.  All 'Repr' dictionaries have
--   the same representation.  There's a predefined global variable for that,
--   so we can return a reference to it.  However, we still need to wrap it
--   in a function to deal with polymorphism.
createDict_Repr param_var subst use_dict = use_dict expr
  where
    param_type = getParamType param_var subst
    op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_Repr)
    expr = ExpM $ AppE defaultExpInfo op [TypM param_type] []

-- | Create the representation of a single-parameter class dictionary.
--   Takes the class dictionary as the first parameter, and the repr
--   constructor function as the second parameter.
createSimpleDict tycon_selector repr_selector param_var subst use_dict =
  withReprDictionary param $ \param_dict ->
  withReprDictionary dict_type $ \dict_repr -> do
    tmpvar <- newAnonymousVar ObjectLevel
    let dict_exp = ExpM $ VarE defaultExpInfo tmpvar
    body <- saveAndUseDict data_type dict_exp use_dict
    return $ ExpM $ LetE { expInfo = defaultExpInfo 
                         , expBinder = mk_pat tmpvar dict_repr
                         , expValue = mk_dict tmpvar param_dict
                         , expBody = body}  
  where
    param = getParamType param_var subst
    data_type = varApp (pyonBuiltin tycon_selector) [param]
    dict_type = varApp (pyonBuiltin the_Repr) [data_type]
    
    mk_pat tmpvar dict_repr = LocalVarP tmpvar dict_type dict_repr
    
    mk_dict tmpvar param_dict =
      let oper = ExpM $ VarE defaultExpInfo (pyonBuiltin repr_selector)
          return_arg = ExpM $ VarE defaultExpInfo tmpvar
      in ExpM $ AppE defaultExpInfo oper [TypM param] [param_dict, return_arg]

-------------------------------------------------------------------------------
-- Transformations on IR data structures

genExp :: Exp Rep -> OP ExpM
genExp expression =
  case expression
  of LoadExpr Value ty e ->
       withReprDictionary ty $ \repr_dict -> do
         e' <- genExp e
         returnApp loadOp [TypM ty] [repr_dict, e']
     LoadExpr Boxed ty e -> do
       e' <- genExp e
       returnApp loadBoxOp [TypM ty] [e']
     StoreExpr Value ty e ->
       takeRetArg $ \ret_arg ->
       withReprDictionary ty $ \repr_dict -> do
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
         withReprDictionary ty $ \repr_dict -> do
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
     LetrecE inf defs body -> do
       defs' <- mapM genDef defs
       body' <- genExp body
       return $ ExpM $ LetrecE inf defs' body'
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
       in withReprDictionary mem_ty $ \repr_dict -> do
         let pattern = LocalVarP pat_var mem_ty repr_dict
             ret_arg = ExpM $ VarE defaultExpInfo pat_var
         rhs' <- withRetArg ret_arg $ genExp rhs
         body' <- genExp body
         return $ ExpM $ LetE inf pattern rhs' body'

     OutPT ::: _ -> internalError "genLet"
     SideEffectPT ::: _ -> internalError "genLet"

     _ -> do
       -- This pattern binds a scalar variable
       let pattern = MemVarP pat_var (convertToMemParamType pat_type)
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
                        , funParams = [MemVarP tmpvar (OutPT ::: ty)]
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
          saveDictionaryPatterns pats $
          genExp (funBody f)
  return $ FunM $ Fun { funInfo = funInfo f
                      , funTyParams = ty_pats
                      , funParams = pats
                      , funReturn = return_ret
                      , funBody = body}
  where
    mk_pat (PatR v pat_type) =
      let new_pat_type = convertToMemParamType pat_type
      in MemVarP v new_pat_type

    -- Create the return parameter if one is needed
    mk_return_pat (RetR (WriteRT ::: ty)) = do
      return_var <- newAnonymousVar ObjectLevel
      return (Just return_var,
              [MemVarP return_var (OutPT ::: ty)],
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
      params = map mk_pat $ altParams alt
  body <- genExp $ altBody alt
  return $ AltM $ Alt { altConstructor = altConstructor alt
                      , altTyArgs = ty_args
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
      in MemVarP v (new_repr ::: convertToMemType ty)

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

  withTheNewVarIdentSupply $ \var_supply -> do
    global_env <- setupEnvironment var_supply
    runOP (genModule repr_mod) global_env Nothing
