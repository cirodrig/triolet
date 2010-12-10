{-| Dominator-based value numbering.


-}
module LowLevel.CSE(commonSubexpressionElimination)
where

import Control.Applicative
import Control.Monad.State
import qualified Data.IntMap as IntMap
import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.Identifier
import LowLevel.FreshVar
import LowLevel.Build
import LowLevel.CodeTypes
import LowLevel.Syntax
import LowLevel.Expr
import LowLevel.Print
import Globals

-- | A map holding the arity of known closure functions.
type ArityMap = IntMap.IntMap Int

insertArity v n m = IntMap.insert (fromIdent $ varID v) n m

lookupArity v m = IntMap.lookup (fromIdent $ varID v) m

newtype CSET m a =
  CSET {runCSET :: ArityMap -> CSEEnv -> m (ArityMap, CSEEnv, a)}

evalCSET :: Monad m => CSET m a -> ArityMap -> CSEEnv -> m a
evalCSET m a env = do (_, _, x) <- runCSET m a env
                      return x

instance (Monad m, Functor m) => Functor (CSET m) where
  fmap f m = CSET $ \a s -> do (a', s', x) <- runCSET m a s
                               return (a', s', f x)

instance Monad m => Monad (CSET m) where
  return x = CSET $ \a s -> return (a, s, x)
  m >>= k = CSET $ \a s -> do (a', s', x) <- runCSET m a s
                              runCSET (k x) a' s'

getArityMap :: Monad m => CSET m ArityMap
getArityMap = CSET $ \a s -> return (a, s, a)

modifyArityMap :: Monad m => (ArityMap -> ArityMap) -> CSET m ()
modifyArityMap f = CSET $ \a s -> return (f a, s, ())

getCSEEnv :: Monad m => CSET m CSEEnv
getCSEEnv = CSET $ \a s -> return (a, s, s)

modifyCSEEnv :: Monad m => (CSEEnv -> CSEEnv) -> CSET m ()
modifyCSEEnv f = CSET $ \a s -> return (a, f s, ())

putCSEEnv :: Monad m => CSEEnv -> CSET m ()
putCSEEnv env = CSET $ \a _ -> return (a, env, ())

instance MonadTrans CSET where
  lift m = CSET $ \a env -> do x <- m
                               return (a, env, x)

type CSE a = CSET (Gen FreshVarM) a

type CSEF a = CSET FreshVarM a

-- | Perform CSE on a statement and return the transformed statement.
evalCSE :: [ValueType] -> CSE Stm -> CSEF Stm
evalCSE rt m = CSET $ \a env -> do
  stm <- execBuild rt $ evalCSET m a env
  return (a, env, stm)

-- | Perform CSE.  Discard the environment.
runCSEF :: CSEF a -> CSE a
runCSEF m = CSET $ \a env -> lift $ runCSET m a env

-------------------------------------------------------------------------------

findArity :: Monad m => Var -> CSET m (Maybe Int)
findArity v = do m <- getArityMap
                 return (lookupArity v m)

cseVal :: Val -> CSE (Val, Maybe Expr)
cseVal value = 
  case value
  of VarV v -> do
       env <- getCSEEnv
       let new_value = fromCSEVal $ cseFindVar v env
       return (new_value, interpretVal env value)
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
       env <- getCSEEnv
       case interpretPrim env prim exprs of
         Nothing -> do
           update_for_store env prim exprs
           return (rebuild_atom, Nothing)
         Just i ->
           let new_atom =
                 case cseFindExpr i env
                 of Just val -> ValA [fromCSEVal val]
                    Nothing  -> rebuild_atom
           in return (new_atom, Just i)
  where
    arg_vals = map fst args
    rebuild_atom = PrimA prim arg_vals

    update_for_store env (PrimStore Constant ty) args = 
      case args
      of [base, off, val] ->
           case interpretStore env ty base off val 
           of Just env' -> putCSEEnv env'
              Nothing -> return ()
         _ -> internalError "csePrim"

    update_for_store _ _ _ = return ()
    
    -- For debugging
    debug_replacement new_prim =
      text "Value numbering replace" <+>
      (pprAtom rebuild_atom $$ pprAtom new_prim)

cseAtom :: Atom -> CSE (Atom, Maybe [Maybe Expr])
cseAtom atom =
  case atom
  of ValA vs -> do
       (vs', exprs) <- mapAndUnzipM cseVal vs
       return (ValA vs', Just exprs)
     CallA cc op args -> cseCall cc op args
     PrimA op args -> do
       (atom, mexpr) <- csePrim op =<< mapM cseVal args
       return (atom, fmap (return . Just) mexpr)
     PackA rec vs -> do
       vs' <- mapM cseVal' vs
       return (PackA rec vs', Nothing)
     UnpackA rec v -> do
       v' <- cseVal' v
       return (UnpackA rec v', Nothing)

cseCall :: CallConvention -> Val -> [Val] -> CSE (Atom, Maybe [Maybe Expr])
cseCall cc op args = do
  -- Perform CSE on operator and arguments
  op_result <- cseVal op
  arg_results <- mapM cseVal args
  debug_env <- getCSEEnv
  let args' = map fst arg_results
      marg_exprs = mapM make_expr arg_results
      
      ppr_op_expr op Nothing = pprVal op
      ppr_op_expr op (Just e) = parens (pprVal op <+> text "=" <+> pprExpr e)
      
      -- What call is being processed, for debugging
      msg = text "cseCall" <+> (uncurry ppr_op_expr op_result $$
                                vcat (map (uncurry ppr_op_expr) arg_results) $$
                               pprCSEEnv debug_env)
  check_op op_result args' marg_exprs
  where
    -- Check the operator to decide if this is a partial application
    check_op (op', mop_expr) args' marg_exprs
      | cc /= ClosureCall =
          no_expr op' args'     -- Not a closure function
      | Nothing <- marg_exprs =
          no_expr op' args'     -- Can't construct expressions for arguments
      | Just op_expr <- mop_expr,
        Just (arity, op_oper, op_args) <- fromAppExpr op_expr,
        Just arg_exprs <- marg_exprs =
          application arity op' args' op_oper op_args arg_exprs
      | Just op_expr <- mop_expr,
        VarV op_var <- op', 
        Just arg_exprs <- marg_exprs = do
          marity <- findArity op_var
          case marity of
            Just arity ->
              application arity op' args' op_expr [] arg_exprs
            Nothing -> no_expr op' args'
      | otherwise =
          no_expr op' args'     -- Can't determine arity of operator

    -- Can't construct an expression for this calling convention
    no_expr op' args' = return (CallA cc op' args', Nothing)

    -- A closure-call appliction with known arity was found.
    -- If it's saturated, then generate a fully saturated application.
    -- If it's undersaturated, then add an expression to the environment.
    --
    -- The atom is (CallA ClosureCall op_val arg_vals).
    -- The expression is (appExpr arity op_expr (op_arg_exprs ++ arg_exprs)).
    application arity op_val arg_vals op_expr op_arg_exprs arg_exprs =
      case (length op_arg_exprs + length arg_exprs) `compare` arity
      of LT -> -- Undersaturated
           return (rebuild_call, Just [Just applied_expr])
         EQ | null op_arg_exprs -> -- Original call was saturated
                return (rebuild_call, Nothing) 
            | otherwise -> do -- Original call was unsaturated; now saturated
                env <- getCSEEnv
                return $! case build_call env op_expr op_arg_exprs arg_vals
                          of Just call_atom -> (call_atom, Nothing)
                             Nothing -> (rebuild_call, Nothing)
         GT | null op_arg_exprs -> -- Original call was oversaturated
                return (rebuild_call, Nothing)
            | length op_arg_exprs >= arity ->
                internalError "cseCall"
            | otherwise ->
                -- TODO: Optimize this case
                return (rebuild_call, Nothing)
      where
        -- The expression representing this partial application
        applied_expr = appExpr arity op_expr (op_arg_exprs ++ arg_exprs)
        
        -- Rebuild the call expression with no changes
        rebuild_call = CallA ClosureCall op_val arg_vals
        
        -- Build a new call expression with the given arguments
        build_call env op_expr op_arg_exprs arg_vals = do
          op_cseval <- cseGetExprValue op_expr env
          op_arg_csevals <- mapM (flip cseGetExprValue env) op_arg_exprs
          let op_val = fromCSEVal op_cseval
              op_arg_vals = map fromCSEVal op_arg_csevals
          return (CallA ClosureCall op_val (op_arg_vals ++ arg_vals))
          
    make_expr :: (Val, Maybe Expr) -> Maybe Expr
    make_expr (arg, Just arg_expr) = return arg_expr
    make_expr (VarV arg_v, Nothing) = return $ varExpr arg_v
    make_expr (LitV arg_l, Nothing) = return $ litExpr arg_l
    make_expr _ = mzero

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
     SwitchE scr alts ->
       cseVal' scr >>= evaluate_switch alts
     ReturnE atom -> do
       (atom', _) <- cseAtom atom
       return (ReturnE atom')
  where
    -- Scrutinee of switch statement is statically known.
    -- Replace the switch statement with the branch that will be executed.
    evaluate_switch alts (LitV scrutinee) =
      case lookup scrutinee alts
      of Just taken_path -> cseStm taken_path
         Nothing -> internalError "cseStm: Missing alternative"
       
    -- Otherwise, scrutinee is not statically known
    evaluate_switch alts scrutinee_value = do
      rt <- lift getReturnTypes
      alts' <- mapM (cse_alt rt) alts
      return (SwitchE scrutinee_value alts')
      where
        cse_alt rt (lit, stm) = do
          stm' <- runCSEF $ evalCSE rt $ cseStm stm
          return (lit, stm')
      
    assign_variable v Nothing = return ()
    assign_variable v (Just e) = modifyCSEEnv $ updateCSEEnv v e

cseDef :: FunDef -> CSEF FunDef
cseDef (Def v f) = Def v <$> cseFun f

cseFun :: Fun -> CSEF Fun
cseFun f = do
  body <- evalCSE (funReturnTypes f) $ cseStm $ funBody f
  return $ mkFun (funConvention f) (funInlineRequest f) (funParams f) (funReturnTypes f) body

cseGlobal :: ArityMap -> CSEEnv -> GlobalDef -> FreshVarM GlobalDef
cseGlobal arities env (GlobalFunDef fdef) =
  GlobalFunDef <$> evalCSET (cseDef fdef) arities env

cseGlobal _       _   def@(GlobalDataDef _) = return def

-- | Create the global CSE environment containing globally defined data.
scanGlobalData :: [Import] -> [GlobalDef] -> (ArityMap, CSEEnv)
scanGlobalData impents defs =
  let imported_constants = concatMap scan_import impents
      global_constants = concatMap scan_data defs
  in foldr ($) (IntMap.empty, emptyCSEEnv) (imported_constants ++ global_constants)
  where
    scan_import (ImportData base (Just initializer)) =
      scan_static_data base initializer
    scan_import (ImportData base Nothing) = []
    scan_import impent@(ImportClosureFun ep _) =
      [scan_global_fun (importVar impent) (functionArity ep)]
    scan_import (ImportPrimFun _ _ _) = []

    scan_data (GlobalFunDef (Def v f)) 
      | isClosureFun f =
          [scan_global_fun v (length $ ftParamTypes $ funType f)]
      | otherwise = []
    scan_data (GlobalDataDef (Def base initializer)) =
      scan_static_data base initializer
    
    scan_static_data base (StaticData rec fs) =
      zipWith (add_field (varExpr base)) (recordFields rec) fs
    
    scan_global_fun fun_var fun_arity = \(arities, env) ->
      (insertArity fun_var fun_arity arities, env)

    add_field base fld val
      | isConstField fld = \(arities, env) ->
          let env' = 
                case interpretVal env val
                of Just cse_val ->
                     fromMaybe env $
                     interpretStore env prim_type base offset cse_val
                   Nothing -> env
          in (arities, env')
      | otherwise = id
      where
        offset = litExpr $ nativeIntL $ fieldOffset fld
        prim_type =
          case fieldType fld
          of PrimField pt -> PrimType pt
             _ -> internalError "scanGlobalData: Unexpected record field"

commonSubexpressionElimination :: Module -> IO Module
commonSubexpressionElimination mod =
  withTheLLVarIdentSupply $ \var_supply -> do
    runFreshVarM var_supply $ do
      globals' <- mapM (cseGlobal arities global_env) $ moduleGlobals mod
      return $ mod {moduleGlobals = globals'}
  where
    (arities, global_env) =
      scanGlobalData (moduleImports mod) (moduleGlobals mod)
