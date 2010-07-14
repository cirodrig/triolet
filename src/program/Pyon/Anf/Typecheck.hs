
{-# LANGUAGE EmptyDataDecls, TypeFamilies, ViewPatterns, TypeSynonymInstances #-}
module Pyon.Anf.Typecheck(typeCheckModule)
where

import Control.Monad
import Data.List
import Data.Monoid
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Gluon.Common.MonadLogic
import Gluon.Common.Error
import Gluon.Common.Label
import Gluon.Common.SourcePos
import Gluon.Core
import Gluon.Core.RenameBase
import qualified Gluon.Core.Builtins.Effect
import Gluon.Eval.Error
import Gluon.Eval.Eval
import Gluon.Eval.Equality
import Gluon.Eval.Environment
import Gluon.Eval.Typecheck
import Pyon.Globals
import Pyon.Anf.Print
import Pyon.Anf.Syntax
import Pyon.Anf.Rename
import Pyon.Anf.Builtins

printTypeCheckSteps = False
quitOnFirstError = True

emptyEffect = asWhnf Gluon.Core.Builtins.Effect.empty

data Typed a
instance Structure a => Structure (Typed a)

data TypeAnn a =
  TypeAnn
  { annotatedType :: !WRExp
  , typeAnnValue :: a
  }

data EffectAnn a =
  EffectAnn
  { returnType :: !WRExp
  , effectType :: !WRExp
  , effectAnnValue :: a
  }

data instance ExpOf (Typed s) (Typed s) =
  TExp (TypeAnn (ExpOf s (Typed s))) | SortExp
newtype instance TupleOf (Typed s) (Typed s) =
  TTuple (TupleOf s (Typed s))
newtype instance SumOf (Typed s) (Typed s) =
  TSum (SumOf s (Typed s))
newtype instance ValOf (Typed s) (Typed s) =
  TVal (TypeAnn (ValOf s (Typed s)))
newtype instance StmOf (Typed s) (Typed s) =
  TStm (EffectAnn (StmOf s (Typed s)))
newtype instance ProcOf (Typed s) (Typed s) =
  TProc (TypeAnn (ProcOf s (Typed s)))

type TRExp = RecExp (Typed Rec)
type TRVal = RecVal (Typed Rec)
type TRStm = RecStm (Typed Rec)
type TRProc = RecProc (Typed Rec)

fromTypedExp :: TRExp -> RExp
fromTypedExp (TExp (typeAnnValue -> exp)) =
  mapExp fromTypedExp tuple sum exp
  where
    tuple (TTuple t) = mapTuple fromTypedExp tuple t
    sum (TSum s) = mapSum fromTypedExp sum s

fromTypedVal :: TRVal -> RVal
fromTypedVal (TVal (typeAnnValue -> val)) =
  mapVal fromTypedExp fromTypedVal fromTypedProc val

fromTypedStm :: TRStm -> RStm
fromTypedStm (TStm (effectAnnValue -> stm)) =
  mapStm fromTypedExp fromTypedVal fromTypedStm fromTypedProc stm

fromTypedProc :: TRProc -> RProc
fromTypedProc (TProc (typeAnnValue -> proc)) =
  mapProc fromTypedExp fromTypedStm proc

class HasTypeAnn a where
  getTypeAnn :: a -> WRExp

instance HasTypeAnn TRExp where getTypeAnn (TExp x) = annotatedType x
instance HasTypeAnn TRVal where getTypeAnn (TVal x) = annotatedType x
instance HasTypeAnn TRStm where getTypeAnn (TStm x) = returnType x
instance HasTypeAnn TRProc where getTypeAnn (TProc x) = annotatedType x
                                 
getEffectAnn :: TRStm -> WRExp
getEffectAnn (TStm x) = effectType x

gluonWorker :: TCWorker (Typed Rec)
gluonWorker = tcWorker doExp doTuple doSum kind
  where
    kind = SortExp -- internalError "No typed representation for sorts"
    doExp e ty = TExp (TypeAnn ty e)
    doTuple = TTuple
    doSum = TSum
    
-------------------------------------------------------------------------------

tcAssertUnmentioned :: (Monad m, TypeErrorMonad m) => Var -> RExp -> m ()
tcAssertUnmentioned v e
  | e `mentions` v = throwError $ OtherErr "Variable mentioned"
  | otherwise = return ()

tcAssertUnmentionedList :: (Monad m, TypeErrorMonad m) => [Var] -> RExp -> m ()
tcAssertUnmentionedList v e
  | e `mentionsAny` v = throwError $ OtherErr "Variable mentioned"
  | otherwise = return ()

combineEffects :: EvalMonad m => WRExp -> WRExp -> m WRExp
combineEffects e1 e2 = liftEvaluation $ do
  e <- evalHead' $ Gluon.Core.Builtins.Effect.sconj (fromWhnf e1) (fromWhnf e2)
  return $ substFullyUnderWhnf e

combineEffectList :: EvalMonad m => [WRExp] -> m WRExp
combineEffectList es = liftEvaluation $ do
  e <- evalHead' $ foldr Gluon.Core.Builtins.Effect.sconj Gluon.Core.Builtins.Effect.empty $ map fromWhnf es
  return $ substFullyUnderWhnf e

-- | Get the type of a procedure
procType :: SRProc -> PureTC RExp
procType proc =
  -- Rename bound variables first
  compute_type =<< freshenHead proc
  where
    compute_type proc =
      add_params (getSourcePos proc) (procParams proc) $
        -- The function range is 'Action eff ret'
        let result_type =
              mkConAppE (getSourcePos proc) (anfBuiltin the_Action)
              [substFully $ procEffectType proc,
               substFully $ procReturnType proc] 
        in return result_type

    add_params pos bs mk_rng = foldr (add_param pos) mk_rng bs

    -- Add a function parameter to the function.  Make it dependent if the 
    -- parameter is intuitionistic and mentioned in the range.
    add_param pos (Binder v ty ()) mk_rng = do 
      ifM (isIntuitionisticType' ty) dependent not_dependent
      where
        r_ty = substFully ty

        not_dependent = do
          rng <- mk_rng
          return $ mkArrowE pos False r_ty rng

        dependent = assumePure v r_ty $ do
          rng <- mk_rng
          return $! if rng `mentions` v
                    then mkFunE pos False v r_ty rng
                    else mkArrowE pos False r_ty rng

-------------------------------------------------------------------------------

-- | If the flag is set, then stop executing once an error is observed
quitOnError m 
  | quitOnFirstError = do
      (errs, x) <- tellErrors m
      if null errs
        then return x
        else internalError (concatMap showTypeCheckError errs)
  | otherwise = m

tcScanExp :: PureTypeErrorMonad m => SRExp -> m TRExp
tcScanExp e = quitOnError $ debug $ do
  (_, e') <- tcScan gluonWorker e
  return e'
  where
    debug k
      | printTypeCheckSteps =
          traceShow (text "tcScanExp" <+> pprExp (substFully e)) k
      | otherwise = k

tcScanVal :: PureTypeErrorMonad m => SRVal -> m TRVal
tcScanVal value = quitOnError $ debug $ do
  r_value <- freshenHead value
  (ty, value') <-
    case r_value
    of GluonV {valInfo = inf, valGluonTerm = e} ->
         tcScanGluonV inf e
       AppV {valInfo = inf, valOper = op, valArgs = args} ->
         tcScanAppV inf op args
       LamV {valInfo = inf, valProc = proc} ->
         tcScanLamV inf proc
  return $ TVal (TypeAnn ty value')
  where
    debug k
      | printTypeCheckSteps =
          traceShow (text "tcScanVal" <+> pprVal (substFully value)) k
      | otherwise = k

tcScanGluonV inf e = do
  (ty, e') <- tcScan gluonWorker e
  return (ty, GluonV {valInfo = inf, valGluonTerm = e'})

tcScanAppV inf op args = do
  -- Process subexpressions
  op' <- tcScanVal op
  args' <- mapM tcScanVal args
  
  -- Represent arguments as Gluon values if possible
  let gluon_args = map get_exp args'
        where
          get_exp x = (getTypeAnn x, valueToExpression x)

  -- Compute result type
  result_ty <- liftPure $
               computeAppliedType (getSourcePos inf) (verbatim $ fromWhnf $ getTypeAnn op') gluon_args
  
  return (result_ty, AppV {valInfo = inf, valOper = op', valArgs = args'})

-- | Convert a value to an expression, if it can be represented that way.
-- Procedure lambda terms cannot be converted.
valueToExpression :: TRVal -> Maybe RExp
valueToExpression (TVal (typeAnnValue -> value)) =
  case value
  of GluonV {valGluonTerm = t} ->
       return $ fromTypedExp t
     AppV {valOper = op, valArgs = args} -> do
       op' <- valueToExpression op
       args' <- mapM valueToExpression args
       return $ mkAppE (getSourcePos value) op' args'
     LamV {} -> mzero

-- | Compute the result type of applying an operator of type @op_ty@ to 
-- operands with types @arg_tys@ and values @args@.
computeAppliedType :: SourcePos -> SRExp -> [(WRExp, Maybe RExp)]
                   -> PureTC WRExp
computeAppliedType pos op_ty args = trace_message $ apply op_ty args
  where
    apply op_ty ((arg_ty, arg_val):args) = do
      op_ty' <- evalHead op_ty
      case fromWhnf op_ty' of
        FunE {expMParam = param, expRange = rng} -> do
          -- Argument must be a subtype of domain
          tcAssertSubtype pos (binder'Type param) (verbatim $ fromWhnf arg_ty)

          -- If dependently typed, assign the argument value
          rng' <- assign_argument param arg_val rng
          
          -- Continue processing range
          apply rng' args

        _ -> throwError $ OtherErr "computeAppliedType: Too many arguments" 

    apply op_ty [] = do
      -- Compute the return type
      evalFully op_ty

    -- Non-dependent parameter: nothing to do
    assign_argument (Binder' Nothing _ ()) _ rng = return rng
    
    -- Dependent parameter: assign the value.  The value must be representable
    -- as an Exp, and the type must be intuitionistic.
    assign_argument (Binder' (Just v) ty ()) (Just val) rng = do
      -- Ensure type is not linear
      intu <- isIntuitionisticType' ty
      unless intu $ throwError $ OtherErr "Linear type used dependently"
      
      return $ assign v val rng
    
    assign_argument (Binder' (Just v) _ ()) Nothing _ =
      throwError $ OtherErr "computeAppliedType: Impure dependently typed parameter value"
      
    -- Print the function type and arguments that will be applied
    trace_message =
      let op_doc   = pprExp (substFully op_ty)
          args_doc = vcat $
                     punctuate (text ";")
                     [case val
                           of Nothing -> pprExp (fromWhnf ty)
                              Just v -> pprExp v <+> colon <+> pprExp (fromWhnf ty)
                          | (ty, val) <- args]
      in traceEnvironment $ show (text "computeAppliedType" $$
                    nest 4 (text "op_ty" <+> op_doc $$
                            text "args" <+> args_doc))

tcScanLamV inf proc = do 
  proc' <- liftPure $ tcScanProc proc
  return (getTypeAnn proc', LamV { valInfo = inf, valProc = proc'})

-- | Scan a statement.  Compute the statement's return type, effect, and
-- simplified form.
tcScanStm :: SRStm -> LinTC TRStm
tcScanStm statement = quitOnError $ debug $ do
  statement' <- freshenHead statement
  (ret_ty, eff_ty, statement'') <-
    case statement'
    of ReturnS {stmInfo = inf, stmVal = v} ->
         tcScanReturn inf v
       CallS {stmInfo = inf, stmVal = v} ->
         tcScanCall inf v
       LetS {stmInfo = inf, stmBinder = param, stmStm = rhs, stmBody = body} ->
         tcScanLet inf param rhs body
       LetrecS {stmInfo = inf, stmDefs = defs, stmBody = body} ->
         tcScanLetrec inf defs body
       CaseS {stmInfo = inf, stmScrutinee = scr, stmAlts = alts} ->
         tcScanCase inf scr alts
  return $ TStm $ EffectAnn ret_ty eff_ty statement''
  where
    debug k
      | printTypeCheckSteps =
          traceShow (text "tcScanStm" <+> pprStm (substFully statement)) k
      | otherwise = k
    
tcScanReturn :: SynInfo -> SRVal -> LinTC (WRExp, WRExp, StmOf Rec (Typed Rec))
tcScanReturn inf v = do
  val' <- tcScanVal v
  return (getTypeAnn val', emptyEffect, ReturnS {stmInfo = inf, stmVal = val'})

tcScanCall :: SynInfo -> SRVal -> LinTC (WRExp, WRExp, StmOf Rec (Typed Rec))
tcScanCall inf v = do
  val' <- tcScanVal v
  
  -- The value must be an action, with type 'Action eff ret'.
  case unpackWhnfAppE $ getTypeAnn val' of
    Just (con, [eff, ret]) | con == anfBuiltin the_Action -> do
      eff' <- evalHead' eff
      ret' <- evalHead' ret
      return (substFullyUnderWhnf ret',
              substFullyUnderWhnf eff',
              CallS inf val')
    
    _ -> case fromWhnf $ getTypeAnn val'
         of FunE {} ->
              throwError $ OtherErr "Not an action: probably too few arguments"
            _ -> throwError $ OtherErr "Not an action"

tcScanLet :: SynInfo -> Binder SubstRec () -> SRStm -> SRStm
          -> LinTC (WRExp, WRExp, StmOf Rec (Typed Rec))
tcScanLet inf binder@(Binder v ty ()) rhs body = do
  -- Scan the RHS
  rhs' <- tcScanStm rhs
  
  -- RHS's type must match the assumed type
  tcAssertSubtype (getSourcePos inf) ty (verbatim $ fromWhnf $ getTypeAnn rhs')

  -- Get the type's type
  ty' <- tcScanExp ty
  let binder' = Binder v ty' ()

  -- Bind the RHS and scan the body
  body' <- assume v (fromTypedExp ty') $ do
    body' <- tcScanStm body
    
    -- The bound variable must not be mentioned in the return type
    tcAssertUnmentioned v $ fromWhnf $ getTypeAnn body'
    tcAssertUnmentioned v $ fromWhnf $ getEffectAnn body'

    return body'

  -- The overall effect is the union of the two effects 
  eff <- combineEffects (getEffectAnn rhs') (getEffectAnn body')
  
  return (getTypeAnn body', eff, LetS { stmInfo = inf
                                      , stmBinder = binder'
                                      , stmStm = rhs'
                                      , stmBody = body'
                                      })

tcScanLetrec :: SynInfo -> ProcDefGroup SubstRec -> SRStm
             -> LinTC (WRExp, WRExp, Stm (Typed Rec))
tcScanLetrec inf defs body = assumeDefGroup defs $ do
  -- Type check local definitions
  defs' <- leaveLinearScope $ mapM tcScanDef defs
  
  -- Type check body
  body' <- tcScanStm body
  
  -- Body must not mention local variables
  let local_vars = [v | ProcDef v _ <- defs]
  tcAssertUnmentionedList local_vars $ fromWhnf $ getTypeAnn body'
  tcAssertUnmentionedList local_vars $ fromWhnf $ getEffectAnn body'
  
  return (getTypeAnn body', getEffectAnn body', LetrecS { stmInfo = inf
                                                        , stmDefs = defs'
                                                        , stmBody = body'})

-- | Add a definition group's types to the environment
assumeDefGroup :: PureTypeErrorMonad m =>
                  ProcDefGroup SubstRec -> m a -> m a
assumeDefGroup defs m = foldr assumeDef m defs

-- | Add a procedure's type to the environment
assumeDef :: PureTypeErrorMonad m =>
             ProcDef SubstRec -> m a -> m a
assumeDef (ProcDef v p) m = do
  ty <- liftPure $ procType p
  assumePure v ty m

tcScanCase :: SynInfo -> SRVal -> [Alt SubstRec]
           -> LinTC (WRExp, WRExp, Stm (Typed Rec))
tcScanCase info scrutinee alts = do
  let pos = getSourcePos info

  -- Get the scrutinee's type
  scrutinee' <- tcScanVal scrutinee
  
  when (null alts) $ internalError "Empty case statement"

  -- Infer the alternatives' types
  alt_results <- parallel (map (tcScanAlt $ getTypeAnn scrutinee') alts)
  let (alt_types, alt_effs, alts') = unzip3 alt_results
  
  -- Return types must match
  let s_alt_types = map (verbatim . fromWhnf) alt_types
  trace "tcScanCase" $ zipWithM (tcAssertEqual pos) s_alt_types (tail s_alt_types)
  
  -- Take union of effect types
  eff <- combineEffectList alt_effs
  
  return (head alt_types, eff, CaseS { stmInfo = info
                                     , stmScrutinee = scrutinee'
                                     , stmAlts = alts'})

tcScanAlt :: WRExp -> Alt SubstRec -> LinTC (WRExp, WRExp, Alt (Typed Rec))
tcScanAlt scrutinee_type alternative = 
  case alternative
  of ConAlt {altConstructor = con, altParams = params, altBody = body} ->
       scanConAlt con params body
     TupleAlt {altParams = params, altBody = body} ->
       scanTupleAlt params body
  where
    scanConAlt con params body =
      matchPattern scrutinee_type con params $ do
        params' <- liftPure $ mapM eval_param params
        let bound_vars = [v | Binder v _ () <- params]

        (rt, et, body') <- scanAltBody bound_vars body
        
        return (rt, et,
                ConAlt { altConstructor = con
                       , altParams = params'
                       , altBody = body'})

    scanTupleAlt params body = 
      matchTuplePattern scrutinee_type params $ do
        params' <- liftPure $ mapM eval_param params
        let bound_vars = [v | Binder v _ () <- params]
        
        (rt, et, body') <- scanAltBody bound_vars body
        
        return (rt, et,
                TupleAlt { altParams = params'
                         , altBody = body'})

    -- Typecheck the body and return a new body statement.
    -- Ensure that pattern-bound variables don't escape in the body's type
    -- or effect type.
    scanAltBody bound_vars body = do
      body' <- tcScanStm body
    
      -- Ensure that bound variables don't escape
      let rt = getTypeAnn body'
          et = getEffectAnn body'
      tcAssertUnmentionedList bound_vars $ fromWhnf rt
      tcAssertUnmentionedList bound_vars $ fromWhnf et
      
      -- Return the return type, effect type, and body statement
      return (rt, et, body')

    eval_param (Binder v ty ()) = do
      ty' <- tcScanExp ty
      return $ Binder v ty' ()

matchPattern :: WRExp -> Con -> [Binder SubstRec ()] -> LinTC a -> LinTC a
matchPattern scr_type con p_params continuation = do
  let c_params = map (mapBinder' id verbatim) $ conParams con
  
  -- Scrutinee type must be a constructor application.
  -- Also, the pattern's constructor must be a data constructor matching 
  -- the scrutinee type.
  case unpackWhnfAppE scr_type of
    Just (scr_con, s_args)
      | con `isDataConstructorOf` scr_con ->
          match_con_args mempty s_args c_params p_params
    _ -> throwError $ OtherErr "Pattern match failure"

  where
    -- Match the pattern, one constructor argument at a time
    match_con_args s_sub s_args (c_param:c_params) p_params =
      -- Is this a rigid parameter?
      case paramRigidity $ binder'Value c_param
      of Rigid n ->
           -- Extract the rigid argument's type from the scrutinee arguments
           -- and add it to the substitution
           if n < 0 || n > length s_args
           then internalError "Bad rigid parameter index"
           else match_rigid s_sub (s_args !! n) c_param $ go_to_next p_params
         Flexible ->
           -- Bind this parameter
           case p_params
           of p_param : p_params' -> do
                match_flexible s_sub p_param c_param $ go_to_next p_params'
              _ -> internalError "Too few parameters in case alternative"
      where
        go_to_next p_params' s_sub' =
          match_con_args s_sub' s_args c_params p_params'
    
    match_con_args _ _ [] [] = continuation
    
    match_con_args _ _ _ _ =
      internalError "Too many parameters in case alternative"

    -- Match a rigid argument.  Specialize the pattern's type based on this
    -- argument.
    match_rigid s_sub rigid_type (Binder' (Just c_var) _ _) k =
      let s_sub' = assignment c_var rigid_type `mappend` s_sub
      in k s_sub'
      
    -- Match a flexible argument.
    match_flexible s_sub (Binder p_var p_ty ()) (Binder' c_mv c_ty _) k = do
      -- Compute the actual constructor parameter's type
      let param_type = joinSubst s_sub c_ty
      
      -- Verify that the types match
      trace "match_flexible" $ tcAssertEqual noSourcePos p_ty param_type
      
      -- Rename the constructor's bound variable to the pattern variable
      let s_sub' = case c_mv
                   of Nothing -> s_sub
                      Just v -> renaming v p_var `mappend` s_sub
      
      -- Assume the bound variable and continue
      assume p_var (substFully param_type) $ k s_sub'

matchTuplePattern :: WRExp -> [Binder SubstRec ()] -> LinTC a -> LinTC a
matchTuplePattern scr_type p_params continuation = do
  -- Scrutinee type must be a tuple type.
  case fromWhnf scr_type of
    TupTyE {expTyFields = s_fields} ->
      match_fields (verbatim s_fields) p_params
    _ -> throwError $ OtherErr "Pattern match failure"
  
  where
    -- Match the pattern, one field at a time
    match_fields (substHead -> (Binder' s_mvar s_ty () :*: s_params))
                 (Binder p_var p_ty () : p_params) = do
      -- Scrutinee and pattern types must match 
      tcAssertEqual noSourcePos p_ty s_ty

      -- Rename the scrutinee variable to the pattern variable
      let s_params' = case s_mvar
                      of Nothing -> s_params
                         Just s_var -> rename s_var p_var s_params
      
      -- Add the pattern-bound variable to the environment; continue
      assume p_var (substFully p_ty) $ match_fields s_params' p_params 

    match_fields (substHead -> Unit) [] = continuation
    
    match_fields (substHead -> Unit) _ =
      internalError "Too many tuple fields in case alternative"

    match_fields _ [] =
      internalError "Too few tuple fields in case alternative"

-- | Run type inference on a procedure definition.
-- Return the procedure's type as it exists in the type environment.
tcScanDef (ProcDef v proc) = do
  proc' <- tcScanProc proc
  return $ ProcDef v proc'

tcScanProc :: SRProc -> PureTC TRProc
tcScanProc proc = quitOnError $ do
  -- Compute the procedure's type
  ty <- procType proc
  whnf_ty <- liftM substFullyUnderWhnf $ evalHead' ty
  
  -- Run type inference in the procedure
  proc' <- tcScanProcNoType proc
  
  return $ TProc (TypeAnn whnf_ty proc')

tcScanProcNoType :: SRProc -> PureTC (Proc (Typed Rec))
tcScanProcNoType proc = scan_proc =<< freshenHead proc
  where
    scan_proc proc = enterLinearScope $ 
      let pos = getSourcePos proc
      in assume_parameters (procParams proc) $ \params -> do
        
        -- Scan the procedure body
        body <- tcScanStm $ procBody proc
      
        -- Verify that inferred return type matches the annotated type
        rt <- tcScanExp $ procReturnType proc
        trace "tcScanProc" $ tcAssertEqual pos
          (verbatim $ fromTypedExp rt)
          (verbatim $ fromWhnf $ getTypeAnn body)

        -- Verify that inferred effect type is smaller than the annotated type
        et <- tcScanExp $ procEffectType proc
        trace "tcScanProc" $ tcAssertSubtype pos
          (verbatim $ fromTypedExp et)
          (verbatim $ fromWhnf $ getEffectAnn body)

        return $ Proc { procInfo = procInfo proc
                      , procParams = params
                      , procReturnType = rt
                      , procEffectType = et
                      , procBody = body
                      }
        
    assume_parameters = withMany assume_parameter
    
    assume_parameter (Binder v s_ty ()) k = do
      ty' <- tcScanExp s_ty
      assume v (fromTypedExp ty') $ k (Binder v ty' ())

withTopLevelDefGroup :: ProcDefGroup SubstRec -> PureTC a
                     -> PureTC (ProcDefGroup (Typed Rec), a)
withTopLevelDefGroup dg m = assumeDefGroup dg $ do
  dg' <- mapM tcScanDef dg
  x <- m
  return (dg', x)

verbatimModule :: RModule -> Module SubstRec
verbatimModule (Module defss) = Module (map (map verbatim_def) defss)
  where
    verbatim_def (ProcDef v p) = ProcDef v (verbatim p)

typeCheckModule :: RModule -> IO (Module (Typed Rec))
typeCheckModule mod =
  let Module defss = verbatimModule mod
  in withTheVarIdentSupply $ \var_supply -> do
    result <- runPureTCIO var_supply $ check_defs defss
    case result of
      Left errs -> fail $ concat $ intersperse "\n" $ map showTypeCheckError errs
      Right defss' -> return $ Module defss'
  where
    check_defs (defs:defss) =
      liftM (uncurry (:)) $ withTopLevelDefGroup defs $ check_defs defss
      
    check_defs [] = return []
      
