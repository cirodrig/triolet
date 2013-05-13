{-| Dominator-based value numbering.


-}
module LowLevel.CSE(commonSubexpressionElimination)
where

import Prelude hiding(mapM, sequence)
import Control.Applicative
import Control.Monad.State hiding(mapM, sequence)
import qualified Data.IntMap as IntMap
import Data.Maybe
import Data.Traversable
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import LowLevel.FreshVar
import LowLevel.Build
import LowLevel.Builtins
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

-- | Add a definition group's arities to the environment.
withDefs :: Group FunDef -> CSET m a -> CSET m a
withDefs defs m = CSET $ \a env ->
  let a' = foldr insert_def a $ groupMembers defs
  in runCSET m a' env
  where
    insert_def (Def v f) arity_map =
      insertArity v (length $ funParams f) arity_map

-------------------------------------------------------------------------------

-- | If a switch expression simply chooses among two alternative values,
--   then replace it with select expressions.
--
--   Switch statements must have two branches, returning a value or
--   calling the same function in each branch.  A select expression is
--   inserted for each argument.
--
-- > switch(v) {
-- >   case LIT: call V [x, y, z]
-- >   case LIT: call V [x, 0, z]
-- > }

simplifySelectingSwitch :: Stm -> FreshVarM Stm
simplifySelectingSwitch
  exp@(SwitchE scr [(tag1, ReturnE atom1), (tag2, ReturnE atom2)]) =

  case (atom1, atom2)
  of (ValA xs, ValA ys) ->
       let mk_atom zs = ReturnE (ValA zs)
       in makeSelectors scr tag1 tag2 xs ys mk_atom

     (CallA cc1 (VarV target1) xs, CallA cc2 (VarV target2) ys)
       | cc1 == cc2 && target1 == target2 && length xs == length ys ->
         let mk_atom zs = ReturnE $ CallA cc1 (VarV target1) zs
         in makeSelectors scr tag1 tag2 xs ys mk_atom

     _ ->
       -- Cannot simplify
       return exp

simplifySelectingSwitch exp = return exp

makeSelectors scrutinee tag1 tag2 values1 values2 mk_atom = do
  condition <- newAnonymousVar (PrimType BoolType)
  let test = booleanTestAtom scrutinee tag1
  select_exp <- select_values (VarV condition) values1 values2
                (\xs -> return $ mk_atom xs)
  return $ LetE [condition] test select_exp
  where
    -- Create select operations for all values
    select_values condition (x:xs) (y:ys) k =
      select_value condition x y $ \z ->
      select_values condition xs ys $ \zs -> k (z : zs)

    select_values _ [] [] k = k []

    -- Create a select operation, if needed
    select_value :: Val -> Val -> Val -> (Val -> FreshVarM Stm) -> FreshVarM Stm
    select_value condition x y k
      | same x y  = k x
      | otherwise = do
          let ty = valType x
          z <- newAnonymousVar ty
          stm <- k (VarV z)
          let atom = PrimA (PrimSelect ty) [condition, x, y]
          return $ LetE [z] atom stm

    same (VarV x)    (VarV y)    = x == y
    same (LitV x)    (LitV y)    = x == y
    same (RecV r xs) (RecV s ys) = r == s && and (zipWith same xs ys)
    same _           _           = False

-- | Create a boolean test that returns true iff @e@ is equal to
--   the given literal
booleanTestAtom e lit =
  case lit
  of BoolL True    -> ValA [e]
     BoolL False   -> PrimA PrimNot [e]
     IntL sgn sz n -> PrimA (PrimCmpZ sgn sz CmpEQ) [e, LitV lit]
     FloatL sz n   -> PrimA (PrimCmpF sz CmpEQ) [e, LitV lit]

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

    update_for_store env (PrimStore Constant ptr_kind ty) new_exprs =
      case new_exprs
      of [base, off, val] ->
           case interpretStore env ptr_kind ty base off val 
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
      | cc == PrimCall =
          -- Can't create an expression for a primitive call.
          -- Try to simplify the call.
          return $ simplifyPrimCall op' args'
      | cc /= ClosureCall =
          no_expr op' args'     -- Not a closure function
      | Just op_expr <- mop_expr,
        Just (arity, op_oper, op_args) <- fromAppExpr op_expr =
          application arity op' args' op_oper op_args marg_exprs
      | Just op_expr <- mop_expr,
        VarV op_var <- op' = do
          marity <- findArity op_var
          case marity of
            Just arity ->
              application arity op' args' op_expr [] marg_exprs
            Nothing -> no_expr op' args'
      | otherwise =
          no_expr op' args'     -- Can't determine arity of operator

    -- Can't construct an expression for this calling convention
    no_expr op' args' = return (CallA cc op' args', Nothing)

    -- A closure-call appliction with known arity was found.
    -- If it's saturated, then generate a fully saturated application.
    -- If it's undersaturated, then add the new value to the environment.
    --
    -- The atom is (CallA ClosureCall op_val arg_vals).
    -- The expression is (appExpr arity op_expr (op_arg_exprs ++ arg_exprs)).
    application arity op_val arg_vals op_expr op_arg_exprs marg_exprs =
      case (length op_arg_exprs + length arg_vals) `compare` arity
      of LT | Just arg_exprs <- marg_exprs -> -- Undersaturated
           -- Construct an expression for the partial application value
           let applied_expr = appExpr arity op_expr (op_arg_exprs ++ arg_exprs)
           in return (rebuild_call, Just [Just applied_expr])
            | otherwise -> no_expr op_val arg_vals
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

-- Try to simplify a primitive function call.
-- Mostly, optimizations are enabled by inlining.
-- However, a few built-in functions are special-cased here.
simplifyPrimCall :: Val -> [Val] -> (Atom, Maybe [Maybe Expr])
simplifyPrimCall op_val arg_vals =
  case op_val
  of VarV op_var
       | op_var == llBuiltin the_prim_triolet_alloc ->
           case arg_vals
           of [LitV (IntL _ _ 0)] ->
                -- Allocation of zero bytes: return NULL
                (ValA [LitV NullL], Just [Just $ litExpr NullL])
              _ -> rebuild_call
       | op_var == llBuiltin the_prim_triolet_dealloc ->
           case arg_vals
           of [LitV NullL] ->
                -- Deallocation of NULL: do nothing
                (ValA [], Just [])
              _ -> rebuild_call
     _ -> rebuild_call
  where
    rebuild_call = (CallA PrimCall op_val arg_vals, Nothing)

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
     LetrecE defgroup stm -> do
       let cse_defs =
             -- If this definition group is recursive, add arities to the
             -- environment
             case defgroup
             of NonRec def -> liftM NonRec $ cseDef def
                Rec defs   -> withDefs defgroup $ liftM Rec $ mapM cseDef defs
       lift . emitLetrec =<< runCSEF cse_defs
       withDefs defgroup $ cseStm stm
     SwitchE scr alts ->
       cseVal' scr >>= evaluate_switch alts
     ReturnE atom -> do
       (atom', _) <- cseAtom atom
       return (ReturnE atom')
     ThrowE val -> do
       liftM ThrowE (cseVal' val)
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
      let new_switch = SwitchE scrutinee_value alts'
      lift $ lift $ simplifySelectingSwitch new_switch
      where
        cse_alt rt (lit, stm) = do
          stm' <- runCSEF $ evalCSE rt $ cseStm stm
          return (lit, stm')

    assign_variable v Nothing = return ()
    assign_variable v (Just e) = modifyCSEEnv $ updateCSEEnv v e
    
    -- Inserted for debugging.  Verify that the function's calling convention
    -- and its type match.
    check_def f_var f x =
      case funConvention f
      of PrimCall | varType f_var == PrimType PointerType -> x
         ClosureCall | varType f_var == PrimType OwnedType -> x
         _ -> internalError "cseStm: Lambda function has wrong type"

cseDef :: FunDef -> CSEF FunDef
cseDef (Def v f) = Def v <$> cseFun f

cseFun :: Fun -> CSEF Fun
cseFun f = do
  body <- evalCSE (funReturnTypes f) $ cseStm $ funBody f
  return $ f {funBody = body}

cseGlobal :: ArityMap -> CSEEnv -> GlobalDef -> FreshVarM GlobalDef
cseGlobal arities env (GlobalFunDef fdef) = do
  fdef' <- insertFrameAccess fdef
  GlobalFunDef <$> evalCSET (cseDef fdef') arities env

cseGlobal _       _   def@(GlobalDataDef _) = return def

-- | Add a statement that fetches the function's stack frame pointer into a
-- variable.  This statement will be removed by DCE if it's not needed.
insertFrameAccess :: FunDef -> FreshVarM FunDef
insertFrameAccess (Def v f) = do
  frame_var <- newAnonymousVar (PrimType PointerType)
  return $ Def v (f {funBody = insert_frame_access frame_var $ funBody f})
  where
    insert_frame_access v stm = LetE [v] (PrimA PrimGetFrameP []) stm

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
    
    scan_static_data base (StaticData value) = 
      case value
      of RecV rec fs ->
           zipWith (add_field ptr_kind (varExpr base)) (recordFields rec) fs
         LitV lit ->
           [add_known_value ptr_kind (PrimType $ litType lit) (varExpr base)
            (litExpr $ nativeIntL 0) value]
      where
        ptr_kind = case varType base of PrimType pt -> pointerKind pt
    
    scan_global_fun fun_var fun_arity = \(arities, env) ->
      (insertArity fun_var fun_arity arities, env)

    add_known_value ptr_kind prim_type base offset val (arities, env) =
      let env' = 
            case interpretVal env val
            of Just cse_val ->
                 fromMaybe env $
                 interpretStore env ptr_kind prim_type base offset cse_val
               Nothing -> env
      in (arities, env')

    add_field ptr_kind base fld val
      | isConstField fld = add_known_value ptr_kind prim_type base offset val
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
      globals' <- mapM (mapM (cseGlobal arities global_env)) $ moduleGlobals mod
      return $ mod {moduleGlobals = globals'}
  where
    (arities, global_env) =
      scanGlobalData (moduleImports mod) (concatMap groupMembers $ moduleGlobals mod)
