
module LowLevel.CSE(commonSubexpressionElimination)
where

import Control.Applicative
import Control.Monad.State

import LowLevel.FreshVar
import LowLevel.Build
import LowLevel.CodeTypes
import LowLevel.Syntax
import LowLevel.Expr
import Globals

type CSE a = StateT CSEEnv (Gen FreshVarM) a

type CSEF a = StateT CSEEnv FreshVarM a

-- | Perform CSE on a statement and return the transformed statement.
evalCSE :: [ValueType] -> CSE Stm -> CSEF Stm
evalCSE rt m = StateT $ \env -> do
  stm <- execBuild rt $ evalStateT m env
  return (stm, env)

runCSEF :: CSEF a -> CSE a
runCSEF m = StateT $ \env -> lift $ runStateT m env

interpretationExpr :: Interpretation -> Maybe Expr
interpretationExpr NoInterpretation = Nothing
interpretationExpr (Translated i)   = Just i
interpretationExpr (Simplified i)   = Just i

cseVal :: Val -> CSE (Val, Maybe Expr)
cseVal (LamV f) = do
  f' <- runCSEF $ cseFun f
  return (LamV f', Nothing)

cseVal (RecV rec vs) = do
  vs' <- mapM cseVal' vs
  return (RecV rec vs', Nothing)

cseVal val = StateT $ \env -> do
  let interpretation = interpretVal env val
      expr = interpretationExpr interpretation
      env' = updateCSEEnv val interpretation env
  val' <- case interpretation
          of Simplified i -> generateExprCode i
             _            -> return val
  return ((val', expr), env')

cseVal' :: Val -> CSE Val
cseVal' val = fmap fst $ cseVal val

-- | Convert a value to a CSE expression, if possible.
partialCSEVal :: Val -> CSE (Either Val Expr)
partialCSEVal val = StateT $ \env ->
  let interpretation = interpretVal env val
      env' = updateCSEEnv val interpretation env
  in return $! case interpretation
               of NoInterpretation -> (Left val, env')
                  Translated i     -> (Right i, env')
                  Simplified i     -> (Right i, env')

-- | Produce a value from a CSE expression produced by 'partialCSEVal'.
generateCSEValues :: [Either Val Expr] -> CSE [Val]
generateCSEValues vals = lift $ mapM generate_value vals
  where
    generate_value (Left val) = return val
    generate_value (Right expr) = generateExprCode expr

csePrim :: Prim -> [Val] -> CSE (Atom, Maybe Expr)
csePrim prim args = do 
  args' <- mapM partialCSEVal args 
  case sequence $ map (either (const Nothing) Just) args' of
    Nothing -> do
      args'' <- generateCSEValues args'
      return (PrimA prim args'', Nothing)
    Just exprs -> do
      env <- get
      let interpretation = interpretPrim env prim exprs
          expr = case interpretation
                 of NoInterpretation -> Nothing
                    Translated i     -> Just i
                    Simplified i     -> Just i
      atom <- lift $
              case interpretation
              of Simplified i -> do val <- generateExprCode i
                                    return (ValA [val])
                 _ -> PrimA prim <$> mapM generateExprCode exprs
      return (atom, expr)

cseAtom :: Atom -> CSE (Atom, Maybe [Maybe Expr])
cseAtom atom =
  case atom
  of ValA vs -> do
       (vs', exprs) <- mapAndUnzipM cseVal vs
       return (ValA vs', Just exprs)
     CallA cc op args -> do
       (op', _) <- cseVal op 
       args' <- mapM cseVal' args
       return (CallA cc op' args', Nothing)
     PrimA op args -> do
       (atom, mexpr) <- csePrim op args
       return (atom, fmap (return . Just) mexpr)
     PackA rec vs -> do
       vs' <- mapM cseVal' vs
       return (PackA rec vs', Nothing)
     UnpackA rec v -> do
       v' <- cseVal' v
       return (UnpackA rec v', Nothing)


cseStm :: Stm -> CSE Stm
cseStm statement =
  case statement
  of LetE lhs rhs stm -> do
       (rhs', exprs) <- cseAtom rhs
       case exprs of
         Nothing -> return ()
         Just es -> zipWithM_ assign_variable lhs es
       lift $ bindAtom lhs rhs
       cseStm stm
     LetrecE defs stm -> do
       lift . emitLetrec =<< runCSEF (mapM cseDef defs)
       cseStm stm
     SwitchE scr alts -> do
       scr' <- cseVal' scr
       rt <- lift getReturnTypes
       alts' <- mapM (cse_alt rt) alts
       return (SwitchE scr' alts')
  where
    cse_alt rt (lit, stm) = do
      stm' <- runCSEF $ evalCSE rt $ cseStm stm
      return (lit, stm')
      
    assign_variable v Nothing = return ()
    assign_vaiable v (Just e) = modify $ updateCSEEnv (VarV v) (Translated e)

cseDef :: FunDef -> CSEF FunDef
cseDef (Def v f) = Def v <$> cseFun f

cseFun :: Fun -> CSEF Fun
cseFun f = do
  body <- evalCSE (funReturnTypes f) $ cseStm $ funBody f
  return $ mkFun (funConvention f) (funParams f) (funReturnTypes f) body

cseGlobal :: CSEEnv -> GlobalDef -> FreshVarM GlobalDef
cseGlobal env (GlobalFunDef fdef) =
  GlobalFunDef <$> evalStateT (cseDef fdef) env

cseGlobal _   def@(GlobalDataDef _) = return def

-- | Create the global CSE environment containing globally defined data.
scanGlobalData :: [GlobalDef] -> CSEEnv
scanGlobalData defs = foldr scan_data emptyCSEEnv defs
  where
    scan_data (GlobalFunDef _) env = env
    scan_data (GlobalDataDef (Def base (StaticData rec fs))) env =
      foldr add_field env $ zip (recordFields rec) fs
    
    add_field (fld, val) env =
      -- TODO: add the field to the environment
      env

commonSubexpressionElimination :: Module -> IO Module
commonSubexpressionElimination mod =
  withTheLLVarIdentSupply $ \var_supply -> do
    runFreshVarM var_supply $ do
      globals' <- mapM (cseGlobal global_env) $ moduleGlobals mod
      return $ mod {moduleGlobals = globals'}
  where
    global_env = scanGlobalData $ moduleGlobals mod
