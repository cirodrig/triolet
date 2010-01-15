
{-# LANGUAGE CPP,
             RelaxedPolyRec,
             RankNTypes,
             TypeSynonymInstances,
             UndecidableInstances,
             BangPatterns,
             FlexibleContexts,
             ScopedTypeVariables,
             TypeFamilies #-}

module Gluon.Pyon.Typecheck
where

import Control.Monad
import Control.Monad.State
import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import qualified Gluon.Common.AppendList as AL
import Gluon.Common.AppendList((<:))
import Gluon.Common.Error
import Gluon.Common.Label
import Gluon.Common.SourcePos
import Gluon.Common.Supply(Supplies)
import Gluon.Core
import Gluon.Core.Module
import qualified Gluon.Core.Builtins.Effect as BI.Effect
import Gluon.Eval.Error
import Gluon.Eval.Environment
import Gluon.Eval.Eval
import Gluon.Eval.Typecheck

import Gluon.Pyon.Syntax
import Gluon.Pyon.Rename

printTypeInferenceSteps = False

#define TypeCheckMonad(m) PureTypeErrorMonad m, Supplies m VarID

type SCStmt = InSubstitution Core CStmt
type StmtSC = Stmt SubstCore

-- A computation result includes a return type, effect type,
-- and the result of the tcWorker.
-- The return type comes first.
data CResult a = CR !CWhnf !CWhnf (StmtOf a)
type CTraversal a = LinTC (CResult a)

data RResult a = RR !CWhnf !CWhnf (StreamOf a)
type RTraversal a = LinTC (RResult a)

data TC2Worker a =
    TC2Worker { pureWorker     :: !(TCWorker a)
              , doStatement    :: !(Stmt a -> CWhnf -> CWhnf -> StmtOf a)
              , doStream       :: !(Stream a -> CWhnf -> CWhnf -> StreamOf a)
              , doProcedure    :: !(Proc a -> ProcOf a)

                -- These fields are only defined for the trivial tcWorker
              , getTrivialStmt :: StmtOf a
              , getTrivialProc :: ProcOf a
              }

instance PyonSyntax TrivialSyntax where
    type StmtOf TrivialSyntax = ()
    type StreamOf TrivialSyntax = ()
    type ProcOf TrivialSyntax = ()

tc2NoWork :: TC2Worker TrivialSyntax
tc2NoWork = TC2Worker { pureWorker     = tcNoWork
                      , doStatement    = \_ _ _ -> ()
                      , doStream       = \_ _ _ -> ()
                      , doProcedure    = \_ -> ()
                      , getTrivialStmt = ()
                      , getTrivialProc = ()
                      }

tc2Worker :: Syntax a =>
             (Exp a -> CWhnf -> ExpOf a)
          -> (Tuple a -> TupOf a)
          -> (Prod a -> ProdOf a)
          -> (Stmt a -> CWhnf -> CWhnf -> StmtOf a)
          -> (Stream a -> CWhnf -> CWhnf -> StreamOf a)
          -> (Proc a -> ProcOf a)
          -> ExpOf a
          -> TC2Worker a
tc2Worker expression tuple product statement stream procedure sort =
    TC2Worker { pureWorker     = tcWorker expression tuple product sort
              , doStatement    = statement
              , doStream       = stream
              , doProcedure    = procedure
              , getTrivialStmt = internalError "tc2Worker"
              , getTrivialProc = internalError "tc2Worker"
              }

-------------------------------------------------------------------------------
-- Type checking for procedures and statements

scanExp :: (TypeCheckMonad(m)) =>
           TC2Worker a -> SCExp -> m (TCResult a)
scanExp worker e = tcScan (pureWorker worker) e

checkExp :: (TypeCheckMonad(m)) =>
            TC2Worker a -> SCExp -> m (ExpOf a)
checkExp worker e = tcCheck (pureWorker worker) e

typeScanProc :: Syntax a =>
                TC2Worker a -> InSubstitution Core CProc -> PureTC (ProcOf a)
typeScanProc = scanProc

-- Verify that a procedure definition is well-typed.
typeCheckProc :: ProcDef Core -> PureTC ()
typeCheckProc procdef = debug $ do
  -- We don't need to assign fresh variables to procedure parameters
  scanProc tc2NoWork (return $ procProcedure procdef)
  return ()
    where
      debug | printTypeInferenceSteps =
                traceShow (text "typeCheckProc" <+>
                           text (show $ procName procdef))
            | otherwise = id

scanProc :: Syntax a =>
            TC2Worker a -> InSubstitution Core CProc -> PureTC (ProcOf a)
scanProc tcWorker proc = scanProc' tcWorker (renameHead proc)

scanProc' :: Syntax a =>
             TC2Worker a -> Proc SubstCore -> PureTC (ProcOf a)
scanProc' tcWorker proc =
  enterLinearScope $ assumeParameters (procParams proc) $ \newBinders -> do
    -- Process the procedure's components
    let ret = procReturn proc
        eff = procEffect proc
    (retTy, retVal) <- scanExp tcWorker ret
    (effTy, effVal) <- scanExp tcWorker eff
    (inferredRet, inferredEff, bodyVal) <-
        if isStmtProc proc
        then do CR inferredRet inferredEff bodyVal <-
                    scanStmt tcWorker $ procBodyStmt proc
                return (inferredRet, inferredEff, Left bodyVal)
        else do RR inferredRet inferredEff bodyVal <-
                    scanStream tcWorker $ procBodyStream proc
                return (inferredRet, inferredEff, Right bodyVal)

    -- The declared return and effect types must have the right kind
    unless (isKindExp LinearKind retTy) $
           throwError (OtherErr "invalid procedure return type")
    unless (isKindExp EffectKind effTy) $
           throwError (OtherErr "invalid procedure effect type")

    -- Declared and inferred types must match
    let retPos = getSourcePos ret
    let effPos = getSourcePos eff
    tcAssertEqual retPos ret (verbatim $ whnfExp inferredRet)
    tcAssertSubtype effPos eff (verbatim $ whnfExp inferredEff)

    -- Run the tcWorker on this procedure
    let newProc =
            case bodyVal
            of Left body -> Proc { procParams   = newBinders
                                 , procReturn   = retVal
                                 , procEffect   = effVal
                                 , procBodyStmt = body
                                 }
               Right body -> Producer { procParams    = newBinders
                                      , procReturn    = retVal
                                      , procEffect    = effVal
                                      , procBodyStream = body
                                      }
    return $ doProcedure tcWorker newProc
    where
      assumeParameters bs k = go AL.nil bs k
          where
            go newParams (b:bs) k =
                assumeParameter b $ \p' -> go (newParams <: p') bs k

            go newParams [] k = k (AL.toList newParams)

            assumeParameter (Binder v ty x) k = do
              -- Process the binder
              (_, tyVal) <- scanExp tcWorker ty

              -- Add parameter variable to environment
              assume v (renameFully ty) $ k (Binder v tyVal x)

-- Compute the type of an application (f arg1 arg2 ...), given the
-- arguments and the type of f.
--
-- The parameter 'funT' has been typechecked.
-- The arguments have not been typechecked.
--
-- The arguments must be substituted (we also evaluate them) because
-- some arguments may have been dependently bound by an earlier part of
-- the application.
computeAppliedCallType :: Syntax a =>
                          TC2Worker a -> SourcePos -> CExp -> [Value SubstCore]
                       -> LinTC ([Value a], CWhnf)
computeAppliedCallType tcWorker pos funT args = do
  funT' <- evalHead' funT
  go funT' args
    where
      go (Whnf funT@(FunE {expMParam = binder@(Binder' mv dom ())
                          , expRange = rng}))
         (arg:args) = do
        -- The domain is valid (already typechecked)
        -- Check that the argument matches the domain type
        (argTy, argVal) <- inferValueType tcWorker arg

        -- TODO: make this a subtype relationship for better accuracy
        let pos = getSourcePos arg
        tcAssertSubtype pos dom (verbatim $ whnfExp argTy)

        -- Assign the variable before processing the range.
        -- We know, thanks to the check in 'inferFunType', that the
        -- bound variable (if there is one) is intuitionistic.
        --
        -- Procedures cannot be bound dependently, and attempting to do
        -- so is an error.
        when (isProcedureValue arg && isDependent binder) $
             throwError (OtherErr "Cannot bind a procedure dependently")

        let dependentArg =
                case arg
                of PureVal _ v -> renameFully v
                   ProcVal {} -> error "Cannot bind a procedure dependently"
            rng' = assignBinder' (Binder' mv (renameFully dom) ())
                                 dependentArg rng
        rng'' <- evalHead rng'
        (argVals, retTy) <- go rng'' args
        return (argVal:argVals, retTy)

      go resultTy [] = do
        return ([], renameWhnfExpFully resultTy)

      go _ _ =
          internalError $
          "Unexpected non-function type application at " ++ show pos

      isProcedureValue (ProcVal {}) = True
      isProcedureValue _ = False

      isDependent (Binder' mv _ _) = isJust mv

-- Infer the result type and effect type of a computation
scanStmt :: Syntax a =>
            TC2Worker a -> InSubstitution Core CStmt -> CTraversal a
scanStmt tcWorker statement = do
  -- We don't ever traverse a statement recursively, so it's not necessary to
  -- generate fresh variable names
  let stmt = renameHead statement
  (ret, eff, s') <-
      case stmt
      of ReturnS {} -> inferReturnType tcWorker stmt
         CallS {}   -> inferCallType tcWorker stmt
         BindS {}   -> inferBindType tcWorker stmt
         CaseS {}   -> inferCaseType tcWorker stmt
         LetS {}    -> inferLetType tcWorker stmt
         LetrecS {} -> inferLetrecType tcWorker stmt

  -- Run the tcWorker function
  return $ CR ret eff $ doStatement tcWorker s' ret eff

inferReturnType :: Syntax a =>
                   TC2Worker a -> StmtSC -> LinTC (CWhnf, CWhnf, Stmt a)
inferReturnType tcWorker (ReturnS {cexpInfo = inf, cexpValue = v}) = do
  (expType, expVal) <- inferValueType tcWorker v
  let effect  = Whnf $ BI.Effect.empty
  return (expType, effect, ReturnS inf expVal)

inferCallType :: Syntax a =>
                 TC2Worker a -> StmtSC -> LinTC (CWhnf, CWhnf, Stmt a)
inferCallType tcWorker (CallS { cexpInfo = inf
                              , cexpCallee = callee
                              , cexpParameters = params}) = do
  -- Infer function's type
  (Whnf calleeTy, calleeVal) <- inferValueType tcWorker callee

  -- Compute the result type of the function tcall
  (paramVals, resultTy) <-
      computeAppliedCallType tcWorker (getSourcePos inf) calleeTy params

  -- Unpack the result type into a return and effect type
  (eff, ret) <-
      case unpackWhnfAppE resultTy
      of Just (con, [eff, ret])
             | con `isBuiltin` the_Action -> do
                 eff' <- evalHead' eff
                 ret' <- evalHead' ret
                 return (Whnf eff, Whnf ret)
         _ -> throwError (OtherErr "Expecting statement function")

  return (ret, eff, CallS inf calleeVal paramVals)

inferBindType :: Syntax a =>
                 TC2Worker a -> StmtSC -> LinTC (CWhnf, CWhnf, Stmt a)
inferBindType tcWorker (BindS { cexpInfo     = inf
                            , cexpBoundVar = lhs
                            , cexpAnte     = ante
                            , cexpPost     = post}) = do
  -- Traverese the first computation
  CR anteRet anteEff anteVal <- scanStmt tcWorker ante

  -- Binder the LHS
  assume lhs (whnfExp anteRet) $ do
    -- Traverse the second computation
    CR postRet postEff postVal <- scanStmt tcWorker post

    -- Ensure that these return types and effects do not mention
    -- the variable 'lhs', which goes out of scope here
    when (whnfExp postRet `mentions` lhs) scopeError
    when (whnfExp postEff `mentions` lhs) scopeError

    -- Combine effects
    -- We evaluate the head in order to eliminate empty effects
    eff <- evalHead $ verbatim $
           BI.Effect.sconj (whnfExp anteEff) (whnfExp postEff)

    return (postRet, renameWhnfExpFully eff, BindS inf lhs anteVal postVal)

    where
      -- Error when a variable is out of scope
      scopeError = throwError ScopeErr

inferCaseType :: Syntax a =>
                 TC2Worker a -> StmtSC -> LinTC (CWhnf, CWhnf, Stmt a)
inferCaseType tcWorker (CaseS { cexpInfo      = inf
                            , cexpScrutinee = val
                            , cexpAlternatives = alts }) = do
  when (null alts) $
       internalError "Unhandled type checking situation: empty case"

  -- First, get the scrutinee's type
  (valType, valVal) <- scanExp tcWorker val

  -- Type check case alternatives in parallel
  (resultTypes, effectTypes, values) <-
      let checkAlt a = inferAltType tcWorker (whnfExp valType) a
      in liftM unzip3 $ parallel $ map checkAlt alts

  -- All result types must match
  compareAllTypes pos $ map (verbatim . whnfExp) resultTypes

  -- All effect types must match
  -- FIXME: compute upper bound of effect types
  compareAllTypes pos $ map (verbatim . whnfExp) effectTypes

  -- Return a result and effect type
  let resultType = head resultTypes
      effectType = head effectTypes

  return (resultType, effectType, CaseS inf valVal values)
    where
      pos = getSourcePos inf

      compareAllTypes pos xs = zipWithM_ (tcAssertEqual pos) xs (tail xs)

-- Infer the result type and effect type of a case alternative.
-- The first two parameters are the type of the value being matched,
-- given as a constructor application.
--
-- We have to deal with pattern matching here.  We first go through all
-- the data constructor's parameters, type check them, and figure out
-- types and values for each data constructor parameter.
--
-- Once we get that list, we back out of the environment we created, go
-- through the alternative's parameters, and rename all our types and
-- values to the variable names that appear in the alternative.  Finally,
-- we have a set of variable bindings to use while type checking the body.
inferAltType :: Syntax a =>
                TC2Worker a -> CExp -> Alt SubstCore
             -> LinTC (CWhnf, CWhnf, Alt a)
inferAltType tcWorker scrutineeType (Alt info pattern body) = do
  (newPat, (retTy, effTy, bodyVal)) <-
       patternMatch tcWorker pos scrutineeType pattern body $ \vars body' -> do
         -- Visit the case body
         CR retTy effTy bodyVal <- scanStmt tcWorker body'

         -- Ensure that these return types and effects do not mention
         -- any pattern-bound variables, which go out of scope here
         when (whnfExp retTy `mentionsAny` vars) $ throwError ScopeErr
         when (whnfExp effTy `mentionsAny` vars) $ throwError ScopeErr

         return (retTy, effTy, bodyVal)

  return (retTy, effTy, Alt info newPat bodyVal)
    where
      pos = getSourcePos info

-- Type check a pattern match.
--
-- The type of the value being matched against is given, and the
-- pattern must agree with this type.
--
-- The continuation is the code over which the pattern variables are
-- in scope.  The continuation is run in an environment extended with
-- the pattern variables.  The set of pattern variables is passed as
-- a parameter to the continuation.
patternMatch :: forall a b. (Syntax a) =>
                TC2Worker a
             -> SourcePos       -- ^ Alternative's source position
             -> CExp            -- ^ Type of scrutinee
             -> Pat SubstCore -- ^ Pattern from a case alternative
             -> SCStmt          -- ^ Body from a case alternative
             -> ([Var] -> SCStmt -> LinTC b) 
                                -- ^ Continuation that will process the
                                --   body of a case alternative
             -> LinTC (Pat a, b)
patternMatch tcWorker pos scrutineeType (ConP con patVars) altBody cont = do
    tyParams <- getTyConParams
    cType    <- liftPure $ getConstructorType con
    patVars' <- liftPure $ beginMatchingConParams patVars con
    (newPatVars, body) <-
        bindParameters tcWorker pos tyParams patVars' cType altBody cont
    return (ConP con newPatVars, body)
    where
      -- ScrutineeType must be an application 'tycon a b c'
      -- where 'tycon' is the type constructor for 'con'.
      getTyConParams = do
        scrutineeType' <- evalFully' scrutineeType
        case unpackWhnfAppE scrutineeType' of
          Just (tyCon, tyParams)
              | conTyCon con == Just tyCon -> return tyParams
              | otherwise -> throwError CaseConErr
          Nothing -> throwError (CaseTypeErr scrutineeType)

patternMatch tcWorker pos scrutineeType (TupP patFields) altBody cont = do
  -- The scrutinee must have tuple type.  Process the tuple type's fields.
  scrutineeType' <- evalHead' scrutineeType
  (patFields', x) <-
      case whnfExp scrutineeType'
      of TupTyE {expTyFields = scrFields} ->
             matchFields altBody
                         (renameProdPatHead $ beginMatchingProdPat patFields)
                         (renameHead scrFields)
                         []
         _ ->
             throwError (CaseTypeErr scrutineeType)

  -- Return the new pattern and body value
  return (TupP patFields', x)
    where
      -- Pattern match each field.
      matchFields :: forall.
                     SCStmt     -- ^ Body of case alternative
                  -> MatchingProdPat SubstCore -- ^ Remaining pattern
                  -> Prod SubstCore -- ^ Remaining scrutinee
                  -> [Var]      -- ^ Bound variables
                  -> LinTC (ProdPat a, b)
      matchFields altBody
                  (MatchingProdP patVar patParam body)
                  (tyParam :*: tyFields)
                  boundVars = do
        let patType = binder'Type patParam

        -- Ensure pattern type is a valid type
        patVal <- checkExp tcWorker patType

        -- Types must match
        tcAssertEqual pos patType (binder'Type tyParam)

        -- Both types must be dependent or not
        case (patParam, tyParam) of
          (Binder' Nothing _ _, Binder' Nothing _ _)   -> return ()
          (Binder' (Just _) _ _, Binder' (Just _) _ _) -> return ()
          (Binder' _ expected _, Binder' _ actual _) -> 
            throwError (TypeMismatchErr pos (renameFully expected) (renameFully actual))

        -- Rename the pattern variable
        newPatVar <- newTemporary (getLevel patVar) (varName patVar)
        let (rnPatParam, rnBody) =
                renameBoundVariable' newPatVar patParam body
            (_, rnTyFields) =
                renameBoundVariable' newPatVar tyParam tyFields
            rnAltBody = rename patVar newPatVar altBody

        -- Assume the pattern variable and continue
        (body', x) <- assume newPatVar (renameFully patType) $
                      matchFields rnAltBody (renameProdPatHead rnBody)
                                            (renameHead rnTyFields)
                                            (newPatVar : boundVars)

        -- Construct the new pattern
        let patBinder = case rnPatParam
                        of Binder' mv patTy () -> Binder' mv patVal ()
            pat' = ProdP newPatVar patBinder body'

        return (pat', x)

      -- When done, run the continuation
      matchFields altBody MatchingUnitP Unit boundVars = do
        x <- cont boundVars altBody
        return (UnitP, x)

      -- If lengths mismatch, type error
      matchFields _ _ _ _ = throwError (OtherErr "Pattern mismatch")

patternMatch tcWorker pos scrutineeType DefaultP altBody cont = do
  -- Cannot match linear values with a default pattern
  lin <- liftPure $ isLinearType scrutineeType
  when lin $ throwError (OtherErr "default used to match a linear value")

  -- Nothing else to do, just run the continuation
  x <- cont [] altBody
  return (DefaultP, x)

-- Tuple patterns are renameable, if we're careful.
-- When renaming a tuple pattern, we also have to rename whatever statements
-- the pattern applies to.
-- Because of the extra conditions, we don't expose the renameability of
-- patterns. 
data MatchingProdPat syn =
    MatchingProdP !Var !(Binder' syn ()) (InSubstitution Core (MatchingProdPat Core))
  | MatchingUnitP

renameProdPatHead :: InSubstitution Core (MatchingProdPat Core)
                  -> MatchingProdPat SubstCore
renameProdPatHead pat =
    case interruptRenaming pat
    of (sub, MatchingProdP v param rest) ->
           let rest' = resumeRenaming sub =<< rest
           in MatchingProdP v (mapBinder' id (resumeRenaming sub) param) rest'
       (sub, MatchingUnitP) -> MatchingUnitP

beginMatchingProdPat :: ProdPat SubstCore
                     -> InSubstitution Core (MatchingProdPat Core)
beginMatchingProdPat (ProdP v param rest) =
    let param' = mapBinder' id renameFully param
    in return $ MatchingProdP v param' (beginMatchingProdPat rest)

beginMatchingProdPat UnitP = return MatchingUnitP

data MatchingConParamPat = MatchingRigidP !Int | MatchingFlexibleP !Var

beginMatchingConParams :: [ConParamPat] -> Con -> PureTC [MatchingConParamPat]
beginMatchingConParams pats con = go AL.nil pats (conParams con)
    where
      go ret (RigidP : ps) (c : cs) =
          case paramRigidity $ binder'Value c
          of Rigid n  -> go (ret AL.<: MatchingRigidP n) ps cs
             Flexible -> patternMismatch

      go ret (FlexibleP v : ps) (c : cs) =
          case paramRigidity $ binder'Value c
          of Rigid n  -> patternMismatch
             Flexible -> go (ret AL.<: MatchingFlexibleP v) ps cs

      go ret [] [] = return (AL.toList ret)

      go _   _  _  = patternMismatch

      patternMismatch = throwError (OtherErr $ "pattern mismatch in constructor " ++ showLabel (conName con))

-- Binder all pattern variables in a constructor pattern.
bindParameters :: TC2Worker a
               -> SourcePos
               -> [CExp]        -- ^ Parameters of scrutinee's type constructor
               -> [MatchingConParamPat] -- ^ Pattern variables
               -> SCExp         -- ^ Constructor type
               -> SCStmt        -- ^ Body of alternative
               -> ([Var] -> SCStmt -> LinTC b)
               -> LinTC ([ConParamPat], b)
bindParameters tcWorker pos tyParams pattern cType altBody cont =
    bindParameter pattern (renameHead cType) []
    where
      -- Binder a rigid parameter:
      -- Get the actual type of this parameter, and substitute it into
      -- the constructor type.
      --
      -- The constructor type must bind this parameter to a variable,
      -- which we check.
      bindParameter (MatchingRigidP n : patVars)
                    (FunE { expMParam = param@(Binder' (Just paramVar) _ _)
                          , expRange  = constructorRange})
                    boundVars = do
        -- Rename this parameter in the constructor type
        let actualTy = tyParams !! n
            constructorRange' =
                renameHead $ assign paramVar actualTy constructorRange

        (patVars', x) <- bindParameter patVars constructorRange' boundVars
        return (RigidP : patVars', x)

      -- Binder a flexible parameter:
      -- Add this parameter to the environment.
      bindParameter (MatchingFlexibleP v : patVars)
                    (FunE { expMParam = param@(Binder' Nothing _ _)
                          , expRange  = constructorRange})
                    boundVars = do
        let constructorRange' = renameHead constructorRange
        (patVars', x) <-
            assume v (renameFully $ binder'Type param) $
            bindParameter patVars constructorRange' (v : boundVars)
        return (FlexibleP v : patVars', x)

      bindParameter [] range boundVars = do x <- cont boundVars altBody
                                            return ([], x)

      -- Error if not a function type
      bindParameter _ _ _ = internalError "bindParameters"

inferLetType :: Syntax a =>
                TC2Worker a -> StmtSC -> LinTC (CWhnf, CWhnf, Stmt a)
inferLetType tcWorker (LetS { cexpInfo = inf
                          , cexpBoundVar = v
                          , cexpLetValue = val
                          , cexpBody = body }) = do
  -- Infer the expression
  (vType, vVal) <- scanExp tcWorker val
  
  -- Assign the variable while checking the body
  let body' = assign v (renameFully val) body
  CR retTy effTy bodyVal <- scanStmt tcWorker body'
  
  -- Construct return value
  return (retTy, effTy, LetS inf v vVal bodyVal)

inferLetrecType :: Syntax a =>
                   TC2Worker a -> StmtSC -> LinTC (CWhnf, CWhnf, Stmt a)
inferLetrecType tcWorker (LetrecS { cexpInfo       = inf
                                , cexpProcedures = procs
                                , cexpScopeVar   = scopeVar
                                , cexpBody       = body }) =
    -- Bring the scope variable and procedures into scope here
    assumePure scopeVar effectKindE $ assumeLocalProcs procs $ do
      -- Type-check each procedure
      newProcs <- (mapM (checkLocalProcedure tcWorker scopeVar) procs)

      -- Infer type of the letrec body
      CR bodyRet bodyEff bodyVal <- scanStmt tcWorker body

      -- Type must not mention any bound variables
      -- TODO: screen out the 'scope' effect
      let boundVars = scopeVar : map procName procs
          retErr    = whnfExp bodyRet `mentionsAny` boundVars
          effErr    = whnfExp bodyEff `mentionsAny` boundVars
      when (retErr || effErr) scopeError

      return (bodyRet, bodyEff, LetrecS inf newProcs scopeVar bodyVal)
    where
      assumeLocalProcs procs m = foldr assumeLocalProc m procs

      assumeLocalProc (ProcDef {procName = v, procProcedure = proc}) m = do
        ty <- leaveLinearScope $ getProcedureType $ renameFully proc
        assumePure v (renameFully ty) m

      -- Error when a variable is out of scope
      scopeError = throwError ScopeErr

-- Typecheck a local procedure.
-- Linear variables cannot be accessed in the procedure body, so
-- step out of the linear scope while checking.
--
-- TODO: Ensure that the procedure has 'scopeVar' as part of its effect.
checkLocalProcedure :: Syntax a =>
                       TC2Worker a
                    -> Var
                    -> ProcDef SubstCore
                    -> LinTC (ProcDef a)
checkLocalProcedure tcWorker scopeVar procdef
    -- If there's no tcWorker function, then we tolerate more errors
    -- in order to provide better error messages
    | tcIsTrivialWorker (pureWorker tcWorker) = do
        newProc <- recover tryTraverseProc
        return $ fromMaybe defaultProc newProc
    | otherwise = tryTraverseProc
          where
            -- Traverse the procedure.  This may throw an error.
            tryTraverseProc = do
              proc' <- leaveLinearScope $
                       scanProc tcWorker (procProcedure procdef)
              return $ ProcDef { procInfo      = procInfo procdef
                               , procName      = procName procdef
                               , procProcedure = proc'
                               }

            defaultProc =
                ProcDef { procInfo = procInfo procdef
                        , procName = procName procdef
                        , procProcedure = getTrivialProc tcWorker
                        }

-- Infer the result type and effect type of a stream
scanStream :: Syntax a =>
              TC2Worker a -> InSubstitution Core (Stream Core) -> RTraversal a
scanStream tcWorker stream = do
  -- We don't ever traverse a stream recursively, so it's not necessary to
  -- generate fresh variable names
  let str = renameHead stream
  (ret, eff, s') <-
      case str
      of DoR {}   -> inferDoType tcWorker str
         CallR {} -> inferStreamCallType tcWorker str

  -- Run the tcWorker function
  return $ RR ret eff $ doStream tcWorker s' ret eff

inferDoType :: Syntax a =>
               TC2Worker a
            -> Stream SubstCore
            -> LinTC (CWhnf, CWhnf, Stream a)
inferDoType tcWorker str@(DoR {sexpInfo = info, sexpStmt = stmt}) = do
  -- Get the statement's return and effect type
  CR ret eff stmtVal <- scanStmt tcWorker stmt

  -- Return those types
  return (ret, eff, DoR info stmtVal)

inferStreamCallType :: Syntax a =>
                       TC2Worker a
                    -> Stream SubstCore
                    -> LinTC (CWhnf, CWhnf, Stream a)
inferStreamCallType tcWorker str@(CallR { sexpInfo = info
                                        , sexpCallee = callee
                                        , sexpParameters = params}) = do

  -- Infer function's type
  (Whnf calleeTy, calleeVal) <- inferValueType tcWorker callee

  -- Compute the result type of the function tcall
  (paramVals, resultTy) <-
      computeAppliedCallType tcWorker (getSourcePos info) calleeTy params

  -- Unpack the result type into a return and effect type
  (eff, ret) <-
      case unpackWhnfAppE resultTy
      of Just (con, [eff, ret])
             | con `isBuiltin` the_Stream -> do
                 eff' <- evalHead' eff
                 ret' <- evalHead' ret
                 return (Whnf eff, Whnf ret)
         _ -> throwError (OtherErr "Expecting stream function")

  return (ret, eff, CallR info calleeVal paramVals)

-- | Infer the type of a value expression
inferValueType :: Syntax a =>
                  TC2Worker a -> Value SubstCore -> LinTC (CWhnf, Value a)
inferValueType tcWorker val =
    case val
    of PureVal pos e -> do (ty, val') <- scanExp tcWorker e
                           return (ty, PureVal pos val')

       -- Inside a lambda, there is no access to linear variables from the
       -- enclosing scope
       ProcVal pos p -> leaveLinearScope $ do
                          p' <- scanProc' tcWorker $ renameHead p
                          ty <- evalFully =<< getProcedureType (renameFully p)
                          return (ty, ProcVal pos p')

-- | Get the type of a procedure.
getProcedureType :: CProc -> PureTC SCExp
getProcedureType proc = liftM verbatim $ toType $ procParams proc
    where
      -- Pick a monad type constructor depending on whether this is a statement
      -- procedure or a stream procedure
      monad = if isStmtProc proc
              then builtin the_Action
              else builtin the_Stream

      -- Each parameter translates to one function parameter.
      -- For each parameter, we decide whether to produce a dependent or
      -- non-dependent type.
      toType (Binder v dom procParam : params)
          | pparamIsDependent procParam = do
              -- Variable is used dependently; must not be linear
              lin <- isLinearType dom
              when lin $ throwError (OtherErr
                                     "linear variable used dependently") 
              rng <- toType params
              return $ mkInternalFunE False v dom rng
          | otherwise = do
              rng <- toType params
              return $ mkInternalArrowE False dom rng

      toType [] =
          return $ mkInternalConAppE monad [procEffect proc, procReturn proc]

