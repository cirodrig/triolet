
{-# LANGUAGE ScopedTypeVariables #-}
module Pyon.NewCore.Typecheck where

import Control.Monad
import Data.Maybe
import Data.Monoid

import Gluon.Common.Error
import Gluon.Common.SourcePos
import qualified Gluon.Core as Gluon
import Gluon.Core.RenameBase(Subst, substitute, assignment, renaming)
import Gluon.Core.Rename(mapSubstitutingSyntax, verbatim, SubstitutingT)
import Gluon.Core(Whnf(..), CWhnf)
import Gluon.Core.Builtins
import Gluon.Core.Builtins.Effect as Builtins.Effect
import Gluon.Eval.Environment
import Gluon.Eval.Eval
import qualified Gluon.Eval.Typecheck as Gluon

import Pyon.NewCore.Syntax
import Pyon.NewCore.Rename
import Pyon.SystemF.Builtins

data PyonWorker a =
  PyonWorker
  { getTCWorker :: !(Gluon.TCWorker a)
  , doVal       :: !(Val a -> CWhnf -> RecVal a)
  , doStm       :: !(Stm a -> CWhnf -> CWhnf -> RecStm a)
  }

-- | Result of type checking a Val
type TCVal syn = (CWhnf, RecVal syn)

type SCVal = RecVal (SubstitutingT Core)
type ValSC = Val (SubstitutingT Core)
type SCStm = RecStm (SubstitutingT Core)
type StmSC = Stm (SubstitutingT Core)

typeScanVal' :: forall syn. Syntax syn =>
               PyonWorker syn -> SCVal -> LinTC (TCVal syn)
typeScanVal' worker value = do
  value' <- freshenValHead value
  (ty, new_val) <-
    case value'
    of GluonV {valInfo = inf, valGluonTerm = t} -> do
         (ty, ty_val) <- Gluon.typeScanExp' (getTCWorker worker) t
         return (ty, GluonV {valInfo = inf, valGluonTerm = ty_val})
       VarV {valInfo = inf, valVar = v} -> 
         typeScanVarV inf v
       LitV {valInfo = inf, valLit = l} ->
         typeScanLitV inf l
       ConV {valInfo = inf, valCon = c} ->
         typeScanConV inf c
       AppV {valInfo = inf, valOper = op, valArgs = args} ->
         typeScanAppV worker inf op args
       ALamV {valInfo = inf, valAFun = fun} ->
         typeScanALamV worker inf fun
       SLamV {valInfo = inf, valSFun = fun} ->
         typeScanSLamV worker inf fun
       SDoV {valInfo = inf, valStm = stm} ->
         typeScanSDoV worker inf stm
  return (ty, doVal worker (new_val :: Val syn) ty)

typeScanVarV :: Syntax syn => SynInfo -> Var -> LinTC (CWhnf, Val syn)
typeScanVarV inf v = do
  ty <- evalFully' =<< getType' (getSourcePos inf) v
  return (ty, VarV inf v)

typeScanLitV inf l =
  let ty = case l
           of IntL _ -> Whnf $ Gluon.mkInternalConE $ builtin the_Int
              FloatL _ -> Whnf $ Gluon.mkInternalConE $ builtin the_Float
  in return (ty, LitV inf l)

typeScanConV inf c = do
  ty <- liftPure $ evalFully =<< Gluon.getConstructorType c
  return (ty, ConV inf c)

typeScanAppV :: Syntax syn => PyonWorker syn -> SynInfo -> SCVal
             -> [SCVal]
             -> LinTC (CWhnf, Val syn)
typeScanAppV worker inf oper args = do
  -- Infer operator type
  (oper_ty, oper_val) <- typeScanVal' worker oper

  -- Infer types and reconstruct expressions in all arguments
  (arg_vals, ret_ty) <- 
    computeAppliedType worker (getSourcePos inf) (whnfExp oper_ty) args
    
  return (ret_ty, AppV inf oper_val arg_vals)

computeAppliedType :: Syntax syn =>
                      PyonWorker syn -> SourcePos -> Gluon.CExp 
                   -> [SCVal]
                   -> LinTC ([RecVal syn], CWhnf)
computeAppliedType worker pos fun_type args = do
  fun_type' <- evalHead' fun_type
  go fun_type' args
  where
    go (Whnf fun_type@(Gluon.FunE { Gluon.expMParam = 
                                       binder@(Binder' mv dom ())
                                  , Gluon.expRange = rng}))
       (arg:args) = do
      -- Argument's type must be a subtype of domain type
      (arg_ty, arg_val) <- typeScanVal' worker arg
      
      let pos = getSourcePos arg
      Gluon.tcAssertSubtype pos dom (verbatim $ whnfExp arg_ty)
      
      -- If this is a dependently typed binding, assign the bound variable
      -- before processing the next argument.  
      -- If dependently typed, the bound variable must be a 'GluonV'.
      let rng' = case renameValFully arg
                 of GluonV {valGluonTerm = arg_value} ->
                      Gluon.assignBinder'Syn 
                      (Binder' mv (Gluon.renameFully dom) ())
                      arg_value
                      rng
                    _ | isJust mv -> internalError 
                                     "Dependently typed function got a non-Gluon parameter"
                      | otherwise -> rng
      rng'' <- evalHead rng'
      (arg_vals, ret_ty) <- go rng'' args
      return (arg_val:arg_vals, ret_ty)
      
    go result_ty [] = return ([], Gluon.renameWhnfExpFully result_ty)

    go _ _ = internalError $
             "Unexpected non-function type application at " ++ show pos

typeScanALamV :: Syntax syn =>
                 PyonWorker syn -> SynInfo -> ActionFun (SubstitutingT Core)
              -> LinTC (CWhnf, Val syn)
typeScanALamV worker inf fun = do
  (fun_type, fun_val) <- leaveLinearScope $ typeScanActionFun worker fun
  return (fun_type, ALamV inf fun_val)

typeScanSLamV :: Syntax syn =>
                 PyonWorker syn -> SynInfo -> StreamFun (SubstitutingT Core)
              -> LinTC (CWhnf, Val syn)
typeScanSLamV worker inf fun = do
  (fun_type, fun_val) <- leaveLinearScope $ typeScanStreamFun worker fun
  return (fun_type, SLamV inf fun_val)

typeScanSDoV :: Syntax syn => PyonWorker syn -> SynInfo -> SCStm
             -> LinTC (CWhnf, Val syn)
typeScanSDoV worker inf stm = do
  -- The body of the 'do' does not have access to linear variables from the
  -- surrounding context
  (stm_type, stm_eff, stm_val) <-
    leaveLinearScope $ enterLinearScope $ typeScanStm' worker stm
  
  -- Wrap the type and effect in a 'Stream' constructor
  let ret_ty = Gluon.mkInternalWhnfAppE (pyonBuiltin the_Stream) 
                                        [whnfExp stm_eff, whnfExp stm_type]
  
  return (ret_ty, SDoV inf stm_val)

typeScanActionFun :: Syntax syn =>
                     PyonWorker syn 
                  -> ActionFun (SubstitutingT Core)
                  -> PureTC (CWhnf, ActionFun syn)
typeScanActionFun worker function = enterLinearScope $
  bindParams worker (funParams function) $ \params -> do
    -- Process the function body
    (ret_type, eff_type, body_val) <-
      typeScanStm' worker $ funBody function

    -- Verify that the annotated return and effect types are well-formed
    let ann_ret_type = funReturnType function
        ann_eff_type = funEffectType function
        ret_pos = getSourcePos ann_ret_type
        eff_pos = getSourcePos ann_eff_type
    ann_ret_val <- Gluon.tcCheck (getTCWorker worker) ann_ret_type
    ann_eff_val <- Gluon.tcCheck (getTCWorker worker) ann_eff_type
    
    -- Actual types must be equal to the annotated types
    Gluon.tcAssertEqual ret_pos ann_ret_type (verbatim $ whnfExp ret_type)
    Gluon.tcAssertEqual ret_pos ann_eff_type (verbatim $ whnfExp eff_type)
 
    -- Function's type is an Action type
    param_types <- forM params $ \(Binder v _ _) -> 
      evalFully' =<< getType' noSourcePos v
    let fn_range =
          Gluon.mkInternalWhnfAppE (pyonBuiltin the_Action) 
          [Gluon.renameFully ann_eff_type, Gluon.renameFully ann_ret_type]
        fn_type = mkFunctionType (zip params param_types) fn_range
                 
    -- Rebuild the function
    let new_fun = Fun { funParams = params
                      , funReturnType = ann_ret_val
                      , funEffectType = ann_eff_val
                      , funBody = body_val
                      }
    return (fn_type, new_fun)

-- | Given parameters produced by 'bindParams' and a return type, create
-- a function type
mkFunctionType :: [(Binder syn (), CWhnf)] -> CWhnf -> CWhnf
mkFunctionType ((Binder v _ _, binder_ty) : params) rng =
  let rng' = mkFunctionType params rng
  in Whnf $ if whnfExp rng' `Gluon.mentions` v
            then Gluon.mkInternalFunE False v (whnfExp binder_ty) (whnfExp rng)
            else Gluon.mkInternalArrowE False (whnfExp binder_ty) (whnfExp rng)
          
mkFunctionType [] rng = rng

typeScanStreamFun :: Syntax syn =>
                     PyonWorker syn 
                  -> StreamFun (SubstitutingT Core)
                  -> PureTC (CWhnf, StreamFun syn)
typeScanStreamFun worker function = enterLinearScope $
  bindParams worker (funParams function) $ \params -> do
    -- Process the function body
    (ret_type, body_val) <-
      typeScanVal' worker $ funBody function

    -- Get the annotated return type
    -- (Ignore the effect annotation)
    let ret_pos = getSourcePos $ funReturnType function
    (ann_ret_type, ann_ret_val) <-
      Gluon.typeScanExp' (getTCWorker worker) $ funReturnType function

    -- Actual type must be equal to the annotated type
    Gluon.tcAssertEqual ret_pos (verbatim $ whnfExp ret_type) 
                                (verbatim $ whnfExp ann_ret_type)

    -- Return type must be a Stream
    case Gluon.unpackWhnfAppE ret_type of 
      Just (con, args) | con `isPyonBuiltin` the_Stream -> return ()
      _ -> throwError $
           OtherErr "Stream function must evaluate to a stream type"

    -- Rebuild the function
    param_types <- forM params $ \(Binder v _ _) ->
      evalFully' =<< getType' noSourcePos v
    let fn_type = mkFunctionType (zip params param_types) ann_ret_type
    let new_fun = Fun { funParams = params
                      , funReturnType = ann_ret_val
                      , funEffectType = internalError "Stream function has no effect type"
                      , funBody = body_val
                      }
    return (fn_type, new_fun)

getActionFunType :: ActionFun (SubstitutingT Core) -> PureTC (Type Core)
getActionFunType function = do
  let ret_type = Gluon.mkInternalConAppE (pyonBuiltin the_Action) 
                 [ Gluon.renameFully $ funEffectType function
                 , Gluon.renameFully $ funReturnType function]
      fun_type = foldr add_param ret_type $
                 map (mapBinder id Gluon.renameFully) $
                 funParams function
      
  -- Ensure it's a valid type
  Gluon.tcCheck Gluon.tcNoWork $ verbatim fun_type
  return fun_type
  where
    add_param (Binder v ty ()) rng
      | rng `Gluon.mentions` v = Gluon.mkInternalFunE False v ty rng
      | otherwise              = Gluon.mkInternalArrowE False ty rng

getStreamFunType :: StreamFun (SubstitutingT Core) -> PureTC (Type Core)
getStreamFunType function = do
  let ret_type = Gluon.renameFully $ funReturnType function
      fun_type = foldr add_param ret_type $
                 map (mapBinder id Gluon.renameFully) $
                 funParams function
      
  -- Ensure it's a valid type
  Gluon.tcCheck Gluon.tcNoWork $ verbatim fun_type
  return fun_type
  where
    add_param (Binder v ty ()) rng
      | rng `Gluon.mentions` v = Gluon.mkInternalFunE False v ty rng
      | otherwise              = Gluon.mkInternalArrowE False ty rng

bindParam :: Syntax syn =>
             PyonWorker syn
          -> Binder (SubstitutingT Core) ()
          -> (Binder syn () -> LinTC a)
          -> LinTC a
bindParam worker (Binder v ty ()) k = do
  -- Check that the type is well-formed
  (ty_type, ty_val) <- Gluon.typeScanExp' (getTCWorker worker) ty
      
  -- Add the parameter to the environment and continue
  assumeIfPure v (Gluon.renameFully ty) $ k (Binder v ty_val ())
        
bindParam' :: Syntax syn =>
             PyonWorker syn
          -> Binder' (SubstitutingT Core) ()
          -> (Binder' syn () -> LinTC a)
          -> LinTC a
bindParam' worker (Binder' mv ty ()) k = do
  -- Check that the type is well-formed
  (ty_type, ty_val) <- Gluon.typeScanExp' (getTCWorker worker) ty
      
  -- Add the parameter to the environment and continue
  assumeIfPureMaybe mv (Gluon.renameFully ty) $ k (Binder' mv ty_val ())

bindParams :: Syntax syn =>
              PyonWorker syn 
           -> [Binder (SubstitutingT Core) ()]
           -> ([Binder syn ()] -> LinTC a)
           -> LinTC a
bindParams worker ps k = go ps []
  where
    -- Bind each parameter.  This reverses the list, so we have to call 
    -- 'reverse' at the end.
    go (p:ps) new_params = bindParam worker p $ \p' -> go ps (p' : new_params)
    go []     new_params = k $ reverse new_params

-- | Perform type inference on a statement.  Return the statement's result
-- type, effect type, and worker value.
typeScanStm' :: Syntax syn =>
                PyonWorker syn
             -> RecStm (SubstitutingT Core)
             -> LinTC (CWhnf, CWhnf, RecStm syn)
typeScanStm' worker statement = do
  statement' <- freshenStmHead statement
  (ret_ty, eff_ty, new_stm) <-
    case statement'
    of ReturnS {stmInfo = inf, stmVal = val} ->
         typeScanReturnS worker inf val
       CallS {stmInfo = inf, stmOper = op, stmArgs = args} ->
         typeScanCallS worker inf op args
       LetS {stmInfo = inf, stmVar = lhs, stmStm = rhs, stmBody = body} ->
         typeScanLetS worker inf lhs rhs body
       LetrecS {stmInfo = inf, stmDefs = defs, stmBody = body} -> 
         typeScanLetrecS worker inf defs body
       CaseS {stmInfo = inf, stmScrutinee = v, stmAlts = alts} -> 
         typeScanCaseS worker inf v alts
  return (ret_ty, eff_ty, doStm worker new_stm ret_ty eff_ty)

typeScanReturnS worker inf val = do
  -- Result is the value's type
  (val_ty, val_val) <- typeScanVal' worker val
  return (val_ty, Whnf Builtins.Effect.empty, ReturnS inf val_val)

typeScanCallS :: Syntax syn =>
                 PyonWorker syn
              -> SynInfo
              -> SCVal
              -> [SCVal]
              -> LinTC (CWhnf, CWhnf, Stm syn)
typeScanCallS worker inf op args = do 
  -- Infer function type
  (op_ty, op_val) <- typeScanVal' worker op
  
  -- Infer types and reconstruct expressions in all arguments
  (arg_vals, result_ty) <- 
    computeAppliedType worker (getSourcePos inf) (whnfExp op_ty) args
  
  -- The result type must be an 'Action'
  (eff_ty, ret_ty) <-
    case Gluon.unpackWhnfAppE result_ty of
      Just (con, [eff_ty, ret_ty]) 
        | con `isPyonBuiltin` the_Action -> return (Whnf eff_ty, Whnf ret_ty)
      Nothing ->
        throwError $ OtherErr "Function call in statement does not have 'Action' type"
  
  return (ret_ty, eff_ty, CallS inf op_val arg_vals)

typeScanLetS worker inf lhs rhs body = do
  -- Process RHS
  (rhs_type, rhs_eff, rhs_val) <- typeScanStm' worker rhs
  
  -- A linear value must be bound to a variable
  is_linear <- liftPure $ Gluon.isLinearType $ whnfExp rhs_type
  when (is_linear && isNothing lhs) $
    throwError $ OtherErr "Linear variable is not bound"
  
  -- Bind the variable, if present
  let assumeIt = case lhs
                 of Just v  -> assumePure v (whnfExp rhs_type)
                    Nothing -> id
  assumeIt $ do
    (body_type, body_eff, body_val) <- typeScanStm' worker body
    
    -- The local variable must not be mentioned in the result
    case lhs of
      Nothing -> return ()
      Just v  -> do
        when (whnfExp body_type `Gluon.mentions` v) $
          throwError $ OtherErr "Return type mentions let-bound variable"
        when (whnfExp body_eff `Gluon.mentions` v) $
          throwError $ OtherErr "Effect type mentions let-bound variable"
    
    -- The overall effect is the union of the two effects
    eff <- evalFully' $
           Builtins.Effect.sconj (whnfExp rhs_eff) (whnfExp body_eff)
    
    return (body_type, eff, LetS inf lhs rhs_val body_val)

typeScanLetrecS worker inf defs body =
  typeScanDefs worker defs $ \defs' -> do
    (body_type, body_eff, body_val) <- typeScanStm' worker body
    let new_stm = LetrecS inf defs' body_val
    return (body_type, body_eff, new_stm)

typeScanDefs :: Syntax syn =>
                PyonWorker syn
             -> [Def (SubstitutingT Core)]
             -> ([Def syn] -> LinTC a)
             -> LinTC a
typeScanDefs worker defs k = 
  assumeDefinienda defs $ mapM scanDefiniens defs >>= k
  where
    assumeDefinienda (def:defs) k = do
      t <- liftPure $ definiensType $ definiens def
      assumePure (definiendum def) t k
      
    scanDefiniens (Def info v def) = leaveLinearScope $ do
      def' <- case def
              of ActionFunDef fun -> do 
                   (_, fun') <- typeScanActionFun worker fun
                   return $ ActionFunDef fun'
                 StreamFunDef fun -> do
                   (_, fun') <- typeScanStreamFun worker fun
                   return $ StreamFunDef fun'
      return $ Def info v def'

definiensType (ActionFunDef fun) = getActionFunType fun 
definiensType (StreamFunDef fun) = getStreamFunType fun 

typeScanCaseS :: Syntax syn =>
                 PyonWorker syn
              -> SynInfo
              -> RecVal (SubstitutingT Core)
              -> [Alt (SubstitutingT Core)]
              -> LinTC (CWhnf, CWhnf, Stm syn)
typeScanCaseS worker inf v alts = do
  let pos = getSourcePos inf
  
  -- Scan the scrutinee
  (scr_type, scr_val) <- typeScanVal' worker v
  
  -- Process alternatives in parallel
  (result_types, effect_types, values) <- 
    liftM unzip3 $ parallel $ map (typeScanAlt worker scr_type) alts
  
  -- Result types must match
  compareAllTypes pos $ map (verbatim . whnfExp) result_types
  
  -- Compute upper bound of effect types
  -- FIXME: This forces effect types to be equal, which is too restrictive
  compareAllTypes pos $ map (verbatim . whnfExp) effect_types
  
  let result_type = head result_types
      effect_type = head effect_types
  return (result_type, effect_type, CaseS inf scr_val values)
  where
    compareAllTypes pos xs = zipWithM_ (Gluon.tcAssertEqual pos) xs (tail xs)

typeScanAlt :: Syntax syn =>
               PyonWorker syn
            -> CWhnf            -- ^ Scrutinee type
            -> Alt (SubstitutingT Core)
            -> LinTC (CWhnf, CWhnf, Alt syn)
typeScanAlt worker scr_type alt = 
  matchPattern worker scr_type (altPat alt) $ \new_pat body_subst -> do
    let body = mapSubstitutingSyntax (substitute body_subst) (altBody alt)
    (body_type, body_eff, body_val) <- typeScanStm' worker body
    
    let pat_vars = patternVariables new_pat
    
    -- Ensure that pattern-bound variables are not mentioned in the return type
    when (whnfExp body_type `Gluon.mentionsAny` pat_vars) $
      throwError $ OtherErr "Return type mentions pattern-bound variable"
    when (whnfExp body_eff `Gluon.mentionsAny` pat_vars) $
      throwError $ OtherErr "Effect type mentions pattern-bound variable"
      
    return (body_type, body_eff, Alt (altInfo alt) new_pat body_val)

patternVariables (ConP con ps) = catMaybes $ map patternVariable ps
  where
    patternVariable (FlexibleP v) = Just v
    patternVariable RigidP = Nothing

matchPattern :: Syntax syn =>
                PyonWorker syn
             -> CWhnf           -- ^ Type to match
             -> Pat             -- ^ Pattern to match against
             -> (Pat -> PyonSubst -> LinTC a) -- ^ Continuation
             -> LinTC a
matchPattern worker scr_type (ConP con p_params) continuation = do
  let c_params = map (mapBinder' id verbatim) $ conParams con
  
  -- Scrutinee type must be a constructor application.
  -- Also, the pattern's constructor must be a data constructor matching 
  -- the scrutinee type.
  case Gluon.unpackWhnfAppE scr_type of
    Just (scr_con, c_args) 
      | con `Gluon.isDataConstructorOf` scr_con -> 
          matchConArgs mempty mempty c_args c_params p_params []
    _ -> throwError $ OtherErr "Pattern match failure"

  where
    -- Pattern-match constructor arguments.
    -- At each argument, compare the pattern's parameter type @p_param@ to the
    -- actual type @c_arg@ inferred from the scrutinee.
    matchConArgs c_sub          -- Substitution to apply to constructor
                 p_sub          -- Substitution to apply to pattern
                 c_args         -- Scrutinee constructor arguments
                 (c_param:c_params) -- Constructor parameters
                 (p_param:p_params) -- Pattern parameters
                 new_p_params =     -- New pattern parameters (reversed)
      -- Is this a rigid parameter?
      -- The pattern must agree with the constructor definition
      case (p_param, Gluon.paramRigidity $ Gluon.binder'Value c_param)
      of (RigidP, Gluon.Rigid n) ->
           -- The rigid argument's type is extracted  from the scrutinee's
           -- type.
           if n < 0 || n > length c_args
           then internalError "Bad rigid parameter index"
           else matchRigidArg c_sub p_sub (c_args !! n) c_param goToNext
         (FlexibleP p_var, Gluon.Flexible) ->
           matchFlexibleArg c_sub p_sub p_var c_param goToNext
         _ ->
           throwError $ OtherErr "pattern mismatch in constructor"
      where
        goToNext c_sub' p_sub' new_p_param =
          matchConArgs c_sub' p_sub' c_args c_params p_params 
                       (new_p_param:new_p_params)
    
    -- With all arguments pattern-matched, run the continuation
    matchConArgs _ p_sub _ [] [] new_p_params =
      let new_pat = ConP con (reverse new_p_params)
          
      in continuation new_pat p_sub

    -- Match a rigid argument.  Bind parameters for this argument to the 
    -- actual type, determined from the scrutinee type.
    matchRigidArg c_sub p_sub rigid_type (Binder' (Just c_var) _ _) k =
      -- Substitute this value in parameters of the constructor
      let c_sub' = assignment c_var rigid_type `mappend` c_sub
      in k c_sub' p_sub RigidP
    
    -- Match a flexible argument.
    matchFlexibleArg c_sub p_sub p_var (Binder' c_mv c_ty _) k = do
      -- Compute the actual constructor parameter's type
      let param_type = Gluon.renameFully $ mapSubstitutingSyntax (substitute c_sub) c_ty
      
      -- Rename the pattern variable
      (p_sub', p_var') <- freshenVar p_sub p_var
      let c_sub' = case c_mv
                   of Nothing -> c_sub
                      Just v -> renaming v p_var' `mappend` c_sub
      
      -- Assume the bound variable and continue
      assume p_var' param_type $ k c_sub' p_sub' (FlexibleP p_var')
