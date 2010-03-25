
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, EmptyDataDecls #-}
module Pyon.NewCore.Typecheck where

import Control.Applicative
import Control.Monad
import Data.List
import Data.Maybe
import Data.Monoid
import Debug.Trace
import Text.PrettyPrint.HughesPJ(text, (<+>), ($$), vcat)

import Gluon.Common.Label
import Gluon.Common.Error
import Gluon.Common.SourcePos
import qualified Gluon.Core as Gluon
import Gluon.Core.RenameBase
import Gluon.Core.Rename
import Gluon.Core(ExpOf(..), TupleOf(..), SumOf(..), Rec, Whnf,
                  Exp, RExp, WRExp, asWhnf, fromWhnf)
import Gluon.Core.Builtins
import Gluon.Core.Builtins.Effect as Builtins.Effect
import Gluon.Eval.Environment
import Gluon.Eval.Eval
import qualified Gluon.Eval.Typecheck as Gluon

import PythonInterface.Python
import Pyon.Globals
import Pyon.NewCore.Syntax
import Pyon.NewCore.Rename
import Pyon.NewCore.Print
import Pyon.SystemF.Builtins

data Structure s => Typed s

instance Structure s => Structure (Typed s)

newtype instance ExpOf (Typed s) s' = TExp (TypeAnn (ExpOf s) s')
newtype instance TupleOf (Typed s) s' = TTuple (TupleOf s s')
newtype instance SumOf (Typed s) s' = TSum (SumOf s s')

newtype instance ValOf (Typed s) s' = TVal (TypeAnn (ValOf s) s')
newtype instance StmOf (Typed s) s' = TStm (EffAnn (StmOf s) s')

data instance ValOf Gluon.TrivialStructure s = TrivialVal
data instance StmOf Gluon.TrivialStructure s = TrivialStm

data TypeAnn t a =
  TypeAnn { typeAnnotation :: WRExp
          , typeAnnValue :: t a
          }

mapTypeAnn :: (t a -> s b) -> TypeAnn t a -> TypeAnn s b
mapTypeAnn f (TypeAnn t x) = TypeAnn t (f x)

traverseTypeAnn :: Monad m =>
                   (t a -> m (s b)) -> TypeAnn t a -> m (TypeAnn s b)
traverseTypeAnn f (TypeAnn t x) = do
  y <- f x
  return $ TypeAnn t y

data EffAnn t a =
  EffAnn { returnAnnotation :: WRExp 
         , effectAnnotation :: WRExp 
         , effAnnValue :: t a
         }

mapEffAnn :: (t a -> s b) -> EffAnn t a -> EffAnn s b
mapEffAnn f (EffAnn return_type effect_type x) = 
  EffAnn return_type effect_type (f x)

traverseEffAnn :: Monad m => (t a -> m (s b)) 
               -> EffAnn t a -> m (EffAnn s b)
traverseEffAnn f (EffAnn return_type effect_type x) = do
  y <- f x
  return $ EffAnn return_type effect_type y

data PyonWorker a =
  PyonWorker
  { getTCWorker :: !(Gluon.TCWorker a)
  , doVal       :: !(Val a -> WRExp -> RecVal a)
  , doStm       :: !(Stm a -> WRExp -> WRExp -> RecStm a)
  }

noWork :: PyonWorker Gluon.TrivialStructure
noWork = PyonWorker Gluon.tcNoWork (\_ _ -> TrivialVal) (\_ _ _ -> TrivialStm)

saveType :: PyonWorker (Typed Rec)
saveType = PyonWorker gluonWorker doVal doStm
  where
    gluonWorker = Gluon.tcWorker doExp doTuple doProd sortValue
    doExp :: Exp (Typed Rec) -> WRExp -> Gluon.RecExp (Typed Rec)
    doExp e t = TExp (TypeAnn t e)
    doTuple = TTuple
    doProd = TSum
    sortValue = let k = Gluon.LitE (Gluon.internalSynInfo Gluon.SortLevel) Gluon.SortL
                    err = internalError "Cannot inspect type of 'kind'"
                in TExp (TypeAnn err k)
    doVal v t = TVal (TypeAnn t v)
    doStm s ty eff = TStm (EffAnn ty eff s)

-- | Result of type checking a Val
type TCVal syn = (WRExp, RecVal syn)

typeScanVal' :: forall syn. Structure syn =>
               PyonWorker syn -> SRVal -> LinTC (TCVal syn)
typeScanVal' worker value = do
  value' <- freshenHead value
  (ty, new_val) <-
    case value'
    of GluonV {valInfo = inf, valGluonTerm = t} -> do
         (ty, ty_val) <- Gluon.typeScanExp' (getTCWorker worker) t
         return (ty, GluonV {valInfo = inf, valGluonTerm = ty_val})
{-       VarV {valInfo = inf, valVar = v} -> 
         typeScanVarV inf v
       LitV {valInfo = inf, valLit = l} ->
         typeScanLitV inf l
       ConV {valInfo = inf, valCon = c} ->
         typeScanConV inf c-}
       AppV {valInfo = inf, valOper = op, valArgs = args} ->
         typeScanAppV worker inf op args
       ALamV {valInfo = inf, valAFun = fun} ->
         typeScanALamV worker inf fun
       SLamV {valInfo = inf, valSFun = fun} ->
         typeScanSLamV worker inf fun
       SDoV {valInfo = inf, valStm = stm} ->
         typeScanSDoV worker inf stm
  return (ty, doVal worker (new_val :: Val syn) ty)

{-typeScanVarV :: Syntax syn => SynInfo -> Var -> LinTC (WRExp, Val syn)
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
  return (ty, ConV inf c)-}

typeScanAppV :: Structure syn => PyonWorker syn -> SynInfo -> SRVal
             -> [SRVal]
             -> LinTC (WRExp, Val syn)
typeScanAppV worker inf oper args = do
  -- Infer operator type
  (oper_ty, oper_val) <- typeScanVal' worker oper

  -- Infer types and reconstruct expressions in all arguments
  (arg_vals, ret_ty) <- 
    computeAppliedType worker (getSourcePos inf) (fromWhnf oper_ty) args
    
  return (ret_ty, AppV inf oper_val arg_vals)

computeAppliedType :: Structure syn =>
                      PyonWorker syn -> SourcePos -> RExp 
                   -> [SRVal]
                   -> LinTC ([RecVal syn], WRExp)
computeAppliedType worker pos fun_type args = do
  fun_type' <- evalHead' fun_type
  go (fromWhnf fun_type') args
  where
    go fun_type@(Gluon.FunE { Gluon.expMParam = 
                                 binder@(Binder' mv dom ())
                            , Gluon.expRange = rng})
       (arg:args) = do
      -- Argument's type must be a subtype of domain type
      (arg_ty, arg_val) <- typeScanVal' worker arg
      
      let pos = getSourcePos arg
      Gluon.tcAssertSubtype pos dom (verbatim $ fromWhnf arg_ty)
      
      -- If this is a dependently typed binding, assign the bound variable
      -- before processing the next argument.  
      -- If dependently typed, the bound variable must be a 'GluonV'.
      let rng' = case valToMaybeExp $ substFully arg
                 of Just arg_value ->
                      Gluon.assignBinder'
                      (Binder' mv (substFully dom) ())
                      arg_value
                      rng
                    Nothing 
                      | isJust mv ->
                          internalError
                          "Dependently typed function got a non-Gluon parameter"
                      | otherwise -> rng
      rng'' <- evalHead rng'
      (arg_vals, ret_ty) <- go (fromWhnf rng'') args
      return (arg_val:arg_vals, ret_ty)
      
    go result_ty [] = return ([], asWhnf $ Gluon.substFullyUnder result_ty)

    go _ _ = internalError $
             "Unexpected non-function type application at " ++ show pos

typeScanALamV :: Structure syn =>
                 PyonWorker syn -> SynInfo -> ActionFun SubstRec
              -> LinTC (WRExp, Val syn)
typeScanALamV worker inf fun = do
  (fun_type, fun_val) <- leaveLinearScope $ typeScanActionFun worker fun
  return (fun_type, ALamV inf fun_val)

typeScanSLamV :: Structure syn =>
                 PyonWorker syn -> SynInfo -> StreamFun SubstRec
              -> LinTC (WRExp, Val syn)
typeScanSLamV worker inf fun = do
  (fun_type, fun_val) <- leaveLinearScope $ typeScanStreamFun worker fun
  return (fun_type, SLamV inf fun_val)

typeScanSDoV :: Structure syn => PyonWorker syn -> SynInfo -> SRStm
             -> LinTC (WRExp, Val syn)
typeScanSDoV worker inf stm = do
  -- The body of the 'do' does not have access to linear variables from the
  -- surrounding context
  (stm_type, stm_eff, stm_val) <-
    leaveLinearScope $ enterLinearScope $ typeScanStm' worker stm
  
  -- Wrap the type and effect in a 'Stream' constructor
  let ret_ty = Gluon.mkInternalWhnfAppE (pyonBuiltin the_Stream) 
                                        [fromWhnf stm_eff, fromWhnf stm_type]
  
  return (ret_ty, SDoV inf stm_val)

typeScanActionFun :: Structure syn =>
                     PyonWorker syn 
                  -> ActionFun SubstRec
                  -> PureTC (WRExp, ActionFun syn)
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
    Gluon.tcAssertEqual ret_pos ann_ret_type (verbatim $ fromWhnf ret_type)
    Gluon.tcAssertEqual ret_pos ann_eff_type (verbatim $ fromWhnf eff_type)
 
    -- Function's type is an Action type
    param_types <- forM params $ \(Binder v _ _) -> 
      evalFully' =<< getType' noSourcePos v
    let fn_range =
          Gluon.mkInternalWhnfAppE (pyonBuiltin the_Action) 
          [substFully ann_eff_type, substFully ann_ret_type]
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
mkFunctionType :: [(Binder syn (), WRExp)] -> WRExp -> WRExp
mkFunctionType ((Binder v _ _, binder_ty) : params) rng =
  let rng' = fromWhnf $ mkFunctionType params rng
  in asWhnf $ if rng' `Gluon.mentions` v
              then Gluon.mkInternalFunE False v (fromWhnf binder_ty) rng'
              else Gluon.mkInternalArrowE False (fromWhnf binder_ty) rng'
          
mkFunctionType [] rng = rng

typeScanStreamFun :: Structure syn =>
                     PyonWorker syn 
                  -> StreamFun SubstRec
                  -> PureTC (WRExp, StreamFun syn)
typeScanStreamFun worker function = enterLinearScope $
  bindParams worker (funParams function) $ \params -> do
    -- Process the function body
    (ret_type, body_val) <-
      typeScanVal' worker $ funBody function

    -- Get the annotated return type
    -- (Ignore the effect annotation)
    let ret_pos = getSourcePos $ funReturnType function
    ann_ret_val <- Gluon.tcCheck (getTCWorker worker) $ funReturnType function
    ann_ret_type <- evalFully $ funReturnType function

    -- Actual type must be equal to the annotated type
    Gluon.tcAssertEqual ret_pos (verbatim $ fromWhnf ann_ret_type) 
                                  (verbatim $ fromWhnf ret_type)

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

getActionFunType :: ActionFun SubstRec -> PureTC (Type Rec)
getActionFunType function = do
  let ret_type = Gluon.mkInternalConAppE (pyonBuiltin the_Action) 
                 [ substFully $ funEffectType function
                 , substFully $ funReturnType function]
      fun_type = foldr add_param ret_type $
                 map (mapBinder id substFully) $
                 funParams function
      
  -- Ensure it's a valid type
  Gluon.tcCheck Gluon.tcNoWork $ verbatim fun_type
  return fun_type
  where
    add_param (Binder v ty ()) rng
      | rng `Gluon.mentions` v = Gluon.mkInternalFunE False v ty rng
      | otherwise              = Gluon.mkInternalArrowE False ty rng

getStreamFunType :: StreamFun SubstRec -> PureTC (Type Rec)
getStreamFunType function = do
  let ret_type = substFully $ funReturnType function
      fun_type = foldr add_param ret_type $
                 map (mapBinder id substFully) $
                 funParams function
      
  -- Ensure it's a valid type
  Gluon.tcCheck Gluon.tcNoWork $ verbatim fun_type
  return fun_type
  where
    add_param (Binder v ty ()) rng
      | rng `Gluon.mentions` v = Gluon.mkInternalFunE False v ty rng
      | otherwise              = Gluon.mkInternalArrowE False ty rng

bindParam :: Structure syn =>
             PyonWorker syn
          -> Binder SubstRec ()
          -> (Binder syn () -> LinTC a)
          -> LinTC a
bindParam worker (Binder v ty ()) k = do
  -- Check that the type is well-formed
  (ty_type, ty_val) <- Gluon.typeScanExp' (getTCWorker worker) ty
      
  -- Add the parameter to the environment and continue
  assumeIfPure v (substFully ty) $ k (Binder v ty_val ())
        
bindParam' :: Structure syn =>
             PyonWorker syn
          -> Binder' SubstRec ()
          -> (Binder' syn () -> LinTC a)
          -> LinTC a
bindParam' worker (Binder' mv ty ()) k = do
  -- Check that the type is well-formed
  (ty_type, ty_val) <- Gluon.typeScanExp' (getTCWorker worker) ty
      
  -- Add the parameter to the environment and continue
  assumeIfPureMaybe mv (substFully ty) $ k (Binder' mv ty_val ())

bindParams :: Structure syn =>
              PyonWorker syn 
           -> [Binder SubstRec ()]
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
typeScanStm' :: Structure syn =>
                PyonWorker syn
             -> RecStm SubstRec
             -> LinTC (WRExp, WRExp, RecStm syn)
typeScanStm' worker statement = do
  statement' <- freshenHead statement
  (ret_ty, eff_ty, new_stm) <-
    case statement'
    of ReturnS {stmInfo = inf, stmVal = val} ->
         typeScanReturnS worker inf val
       CallS {stmInfo = inf, stmVal = val} ->
         typeScanCallS worker inf val
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
  return (val_ty, asWhnf Builtins.Effect.empty, ReturnS inf val_val)

typeScanCallS :: Structure syn =>
                 PyonWorker syn
              -> SynInfo
              -> SRVal
              -> LinTC (WRExp, WRExp, Stm syn)
typeScanCallS worker inf val = do 
  -- Infer the action's type
  (result_ty, val_val) <- typeScanVal' worker val
  
  -- The result type must be an 'Action'
  (eff_ty, ret_ty) <-
    case Gluon.unpackWhnfAppE result_ty of
      Just (con, [eff_ty, ret_ty]) 
        | con `isPyonBuiltin` the_Action -> return (asWhnf eff_ty, asWhnf ret_ty)
      _ ->
        traceShow (pprVal (substFully val) $$ Gluon.pprExp (fromWhnf result_ty)) $ throwError $ OtherErr "Function call in statement does not have 'Action' type"

  return (ret_ty, eff_ty, CallS inf val_val)

typeScanLetS worker inf lhs rhs body = do
  -- Process RHS
  (rhs_type, rhs_eff, rhs_val) <- typeScanStm' worker rhs
  
  -- A linear value must be bound to a variable
  is_linear <- liftPure $ Gluon.isLinearType $ fromWhnf rhs_type
  when (is_linear && isNothing lhs) $
    throwError $ OtherErr "Linear variable is not bound"
  
  -- Bind the variable, if present
  let assumeIt = case lhs
                 of Just v  -> assumePure v (fromWhnf rhs_type)
                    Nothing -> id
  assumeIt $ do
    (body_type, body_eff, body_val) <- typeScanStm' worker body
    
    -- The local variable must not be mentioned in the result
    case lhs of
      Nothing -> return ()
      Just v  -> do
        when (fromWhnf body_type `Gluon.mentions` v) $
          throwError $ OtherErr "Return type mentions let-bound variable"
        when (fromWhnf body_eff `Gluon.mentions` v) $
          throwError $ OtherErr "Effect type mentions let-bound variable"
    
    -- The overall effect is the union of the two effects
    eff <- evalFully' $
           Builtins.Effect.sconj (fromWhnf rhs_eff) (fromWhnf body_eff)
    
    return (body_type, eff, LetS inf lhs rhs_val body_val)

typeScanLetrecS worker inf defs body =
  typeScanDefs worker defs $ \defs' -> do
    (body_type, body_eff, body_val) <- typeScanStm' worker body
    let new_stm = LetrecS inf defs' body_val
    return (body_type, body_eff, new_stm)

typeScanDefs :: Structure syn =>
                PyonWorker syn
             -> [Def SubstRec]
             -> ([Def syn] -> LinTC a)
             -> LinTC a
typeScanDefs worker defs k =
  assumeDefinienda defs $ mapM scanDefiniens defs >>= k
  where
    assumeDefinienda defs k = foldr assumeDefiniendum k defs
    assumeDefiniendum def k = do
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

typeScanModule :: Structure s =>
                  PyonWorker s -> Module Rec -> PureTC (Module s)
typeScanModule worker mod = enterLinearScope $ do
  Module rename_defs <- freshenModuleHead mod
  typeScanDefs worker rename_defs $ return . Module

typeCheckModule :: Module Rec -> IO ()
typeCheckModule mod = do
  result <- withTheVarIdentSupply $ \supply ->
    runLinTCIO supply $ do
      Module rename_defs <- freshenModuleHead mod
      typeScanDefs noWork rename_defs $ \_ -> return ()
  case result of
    Left errs -> do mapM_ (putStrLn . showTypeCheckError) errs
                    throwPythonExc pyRuntimeError "Type checking failed"
    Right () -> return ()

definiensType (ActionFunDef fun) = getActionFunType fun 
definiensType (StreamFunDef fun) = getStreamFunType fun 

typeScanCaseS :: Structure syn =>
                 PyonWorker syn
              -> SynInfo
              -> RecVal SubstRec
              -> [Alt SubstRec]
              -> LinTC (WRExp, WRExp, Stm syn)
typeScanCaseS worker inf v alts = do
  let pos = getSourcePos inf
  
  -- Scan the scrutinee
  (scr_type, scr_val) <- typeScanVal' worker v
  
  -- Process alternatives in parallel
  (result_types, effect_types, values) <- 
    liftM unzip3 $ parallel $ map (typeScanAlt worker scr_type) alts
  
  -- Result types must match
  compareAllTypes pos $ map (verbatim . fromWhnf) result_types
  
  -- Compute upper bound of effect types
  -- FIXME: This forces effect types to be equal, which is too restrictive
  compareAllTypes pos $ map (verbatim . fromWhnf) effect_types
  
  let result_type = head result_types
      effect_type = head effect_types
  return (result_type, effect_type, CaseS inf scr_val values)
  where
    compareAllTypes pos xs = 
      zipWithM_ (Gluon.tcAssertEqual pos) xs (tail xs)

typeScanAlt :: Structure syn =>
               PyonWorker syn
            -> WRExp            -- ^ Scrutinee type
            -> Alt SubstRec
            -> LinTC (WRExp, WRExp, Alt syn)
typeScanAlt worker scr_type alt = 
  matchPattern scr_type (altPat alt) $ do
    (body_type, body_eff, body_val) <- typeScanStm' worker (altBody alt)
    
    let pat_vars = patternVariables (altPat alt)
    
    -- Ensure that pattern-bound variables are not mentioned in the return type
    when (fromWhnf body_type `Gluon.mentionsAny` pat_vars) $
      throwError $ OtherErr "Return type mentions pattern-bound variable"
    when (fromWhnf body_eff `Gluon.mentionsAny` pat_vars) $
      throwError $ OtherErr "Effect type mentions pattern-bound variable"
      
    return (body_type, body_eff, Alt (altInfo alt) (altPat alt) body_val)

matchPattern :: WRExp           -- ^ Type to match
             -> Pat             -- ^ Pattern to match against
             -> LinTC a         -- ^ Computation to run with pattern matched
             -> LinTC a
matchPattern scr_type (ConP con p_params) continuation = do
  let c_params = map (mapBinder' id verbatim) $ conParams con
  
  -- Scrutinee type must be a constructor application.
  -- Also, the pattern's constructor must be a data constructor matching 
  -- the scrutinee type.
  case Gluon.unpackWhnfAppE scr_type of
    Just (scr_con, c_args) 
      | con `Gluon.isDataConstructorOf` scr_con -> 
          matchConArgs mempty c_args c_params p_params
    _ -> throwError $ OtherErr "Pattern match failure"

  where
    -- Pattern-match constructor arguments.
    -- At each argument, compare the pattern's parameter type @p_param@ to the
    -- actual type @c_arg@ inferred from the scrutinee.
    matchConArgs c_sub          -- Substitution to apply to constructor
                 c_args         -- Scrutinee constructor arguments
                 (c_param:c_params) -- Constructor parameters
                 (p_param:p_params) = -- Pattern parameters
      -- Is this a rigid parameter?
      -- The pattern must agree with the constructor definition
      case (p_param, Gluon.paramRigidity $ Gluon.binder'Value c_param)
      of (RigidP, Gluon.Rigid n) ->
           -- The rigid argument's type is extracted  from the scrutinee's
           -- type.
           if n < 0 || n > length c_args
           then internalError "Bad rigid parameter index"
           else matchRigidArg c_sub (c_args !! n) c_param goToNext
         (FlexibleP p_var, Gluon.Flexible) ->
           matchFlexibleArg c_sub p_var c_param goToNext
         _ ->
           throwError $ OtherErr "pattern mismatch in constructor"
      where
        goToNext c_sub' =
          matchConArgs c_sub' c_args c_params p_params
    
    -- With all arguments pattern-matched, run the continuation
    matchConArgs _ _ [] [] = continuation
    
    -- Error if argument lists aren't the same length
    matchConArgs _ _ _ _ =
      internalError "Wrong number of parameters to pattern" 

    -- Match a rigid argument.  Bind parameters for this argument to the 
    -- actual type, determined from the scrutinee type.
    matchRigidArg c_sub rigid_type (Binder' (Just c_var) _ _) k =
      -- Substitute this value in parameters of the constructor
      let c_sub' = assignment c_var rigid_type `mappend` c_sub
      in k c_sub'
    
    -- Match a flexible argument.
    matchFlexibleArg c_sub p_var (Binder' c_mv c_ty _) k = do
      -- Compute the actual constructor parameter's type
      let param_type = substFully $ joinSubst c_sub c_ty
      
      -- Rename the constructor's bound variable to the pattern variable
      let c_sub' = case c_mv
                   of Nothing -> c_sub
                      Just v -> renaming v p_var `mappend` c_sub
      
      -- Assume the bound variable and continue
      assume p_var param_type $ k c_sub'
