{-| Dominator-based value numbering.


-}
module LowLevel.CSE(commonSubexpressionElimination)
where

import Control.Applicative
import Control.Monad.State
import Data.Maybe
import Debug.Trace

import LowLevel.FreshVar
import LowLevel.Build
import LowLevel.CodeTypes
import LowLevel.Syntax
import LowLevel.Expr
import Globals

updateCSEEnv' :: Var -> Maybe Expr -> CSEEnv -> CSEEnv
updateCSEEnv' v Nothing  env = env
updateCSEEnv' v (Just e) env = updateCSEEnv v e env

type CSE a = StateT CSEEnv (Gen FreshVarM) a

type CSEF a = StateT CSEEnv FreshVarM a

-- | Perform CSE on a statement and return the transformed statement.
evalCSE :: [ValueType] -> CSE Stm -> CSEF Stm
evalCSE rt m = StateT $ \env -> do
  stm <- execBuild rt $ evalStateT m env
  return (stm, env)

runCSEF :: CSEF a -> CSE a
runCSEF m = StateT $ \env -> lift $ runStateT m env

cseVal :: Val -> CSE (Val, Maybe Expr)
cseVal value = 
  case value
  of VarV v -> gets $ \env ->
       let new_value = fromCSEVal $ cseFindVar v env
       in (new_value, interpretVal env value)
     LitV l -> return (value, Just $ litExpr l)
     LamV f -> do
       f' <- runCSEF $ cseFun f
       return (LamV f', Nothing)
     RecV rec vs -> do
       vs' <- mapM cseVal' vs
       return (RecV rec vs', Nothing)

cseVal' :: Val -> CSE Val
cseVal' value = fmap fst $ cseVal value

csePrim :: Prim -> [(Val, Maybe Expr)] -> CSE (Atom, Maybe Expr)
csePrim prim args =
  case sequence $ map snd args
  of Nothing -> return (rebuild_atom, Nothing)
     Just exprs -> do
       env <- get
       case interpretPrim env prim exprs of
         Nothing -> return (rebuild_atom, Nothing)
         Just i -> 
           let new_atom =
                 case cseFindExpr i env
                 of Just val -> ValA [fromCSEVal val]
                    Nothing  -> rebuild_atom
           in return (new_atom, Just i)
  where
    arg_vals = map fst args
    rebuild_atom = PrimA prim arg_vals

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
       (atom, mexpr) <- csePrim op =<< mapM cseVal args
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
       lift $ bindAtom lhs rhs'
       cseStm stm
     LetrecE defs stm -> do
       lift . emitLetrec =<< runCSEF (mapM cseDef defs)
       cseStm stm
     SwitchE scr alts -> do
       scr' <- cseVal' scr
       rt <- lift getReturnTypes
       alts' <- mapM (cse_alt rt) alts
       return (SwitchE scr' alts')
     ReturnE atom -> do
       (atom', _) <- cseAtom atom
       return (ReturnE atom')
  where
    cse_alt rt (lit, stm) = do
      stm' <- runCSEF $ evalCSE rt $ cseStm stm
      return (lit, stm')
      
    assign_variable v Nothing = return ()
    assign_variable v (Just e) = modify $ updateCSEEnv v e

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
