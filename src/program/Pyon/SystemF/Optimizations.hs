
module Pyon.SystemF.Optimizations
    (optimizeModule)
where

import Control.Applicative(Const(..))
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer

import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set

import Gluon.Common.Error
import qualified Gluon.Core as Gluon
import qualified Gluon.Eval.Typecheck as Gluon
import Pyon.SystemF.Syntax
import Pyon.SystemF.Builtins

catEndo :: [a -> a] -> a -> a
catEndo fs x = foldr ($) x fs

-- | Apply optimizations to a module.
optimizeModule :: RModule -> RModule
optimizeModule mod =
  mapModule elimDeadCode $
  mapModule doPartialEvaluation $
  mod

mapModule :: (RDef -> RDef) -> RModule -> RModule
mapModule f (Module ds exports) = Module (map (map f) ds) exports

-------------------------------------------------------------------------------
-- Partial evaluation

doPartialEvaluation :: RDef -> RDef
doPartialEvaluation def = runPEval $ pevalDef def

-- | The 'PEval' monad holds a variable-to-value mapping for constant
-- propagation, copy propagation, and inlining.  Expressions in the map have
-- no side effects, and therefore are safe to inline.
type PEval a = Reader (Map Var RExp) a

-- | Perform partial evaluation in an empty environment.
runPEval :: PEval a -> a
runPEval m = runReader m Map.empty

lookupVar :: Var -> PEval (Maybe RExp)
lookupVar v = asks (Map.lookup v)

lookupVarDefault :: RExp -> Var -> PEval RExp
lookupVarDefault defl v = asks (Map.findWithDefault defl v)

-- | Given a value and the pattern it is bound to, add the bound value(s)
-- to the environment.  The caller should verify that the value has no
-- side effects.  Any values that cannot be added to the environment will be
-- ignored.
bindValue :: RPat -> RExp -> PEval a -> PEval a
bindValue (WildP _)   _ m = m
bindValue (VarP v t)  e m = local (Map.insert v e) m
bindValue (TupleP ps) e m =
  case e
  of TupleE {expFields = es}
       | length ps == length es ->
           catEndo (zipWith bindValue ps es) m
       | otherwise -> error "Tuple pattern mismatch"
     _ ->
       -- Cannot bind, because we cannot statically deconstruct this tuple
       m

bindDefs :: ExpInfo -> [RDef] -> PEval a -> PEval a
bindDefs info defs m = foldr bindDef m defs
  where
    bindDef (Def v f) m =
      let e = FunE info f
      in local (Map.insert v e) m

-- | Partial evaluation of an expression.  First, evaluate subexpressions;
-- then, try to statically evaluate.
pevalExp :: RExp -> PEval RExp
pevalExp expression =
  return . partialEvaluate =<< pevalExpRecursive expression
partialEvaluate :: RExp -> RExp
partialEvaluate expression =
  internalError "Not implemented: dictionary partial evaluation"
  {-
  case expression
  of MethodSelectE {expArg = argument} ->
       case argument
       of DictE {} ->
            -- Select a method from the dictionary
            expMethods argument !! expMethodIndex expression

          _ -> expression
           
     -- Default: return the expression unchanged
     _ -> expression
  where
    unpackTypeApplication e = unpack e []
      where
        unpack e tail =
          case e
          of TyAppE {expOper = op, expTyArg = ty} -> unpack op (ty : tail)
             _ -> Just (e, tail) -}

pevalExpRecursive :: RExp -> PEval RExp
pevalExpRecursive expression =
  case expression
  of VarE {expVar = v} -> lookupVarDefault expression v
     ConE {} -> return expression
     LitE {} -> return expression
     UndefinedE {} -> return expression
     TupleE {expFields = fs} -> do
       fs' <- mapM pevalExp fs
       return $ expression {expFields = fs'}
     TyAppE {expOper = op} -> do
       op' <- pevalExp op
       return $ expression {expOper = op'}
     CallE {expOper = op, expArgs = args} -> do
       op' <- pevalExp op
       args' <- mapM pevalExp args
       return $ expression {expOper = op', expArgs = args'}
     IfE {expCond = c, expTrueCase = tr, expFalseCase = fa} -> do
       c' <- pevalExp c
       tr' <- pevalExp tr
       fa' <- pevalExp fa
       return $ expression { expCond = c'
                           , expTrueCase = tr'
                           , expFalseCase = fa'}
     FunE {expFun = f} -> do
       f' <- pevalFun f
       return $ expression {expFun = f'}
     LetE {expBinder = p, expValue = e1, expBody = e2} -> do
       e1' <- pevalExp e1

       -- If the let-bound value has no side effects, it is a candidate for
       -- inlining
       e2' <- if isValueExp e1'
              then bindValue p e1' $ pevalExp e2
              else pevalExp e2
       return $ expression {expValue = e1', expBody = e2'}
     LetrecE {expInfo = inf, expDefs = ds, expBody = b} -> do
       ds' <- mapM pevalDef ds
       b' <- pevalExp b
       return $ expression {expDefs = ds', expBody = b'}
{-     DictE {expSuperclasses = scs, expMethods = ms} -> do
       scs' <- mapM pevalExp scs
       ms' <- mapM pevalExp ms
       return $ expression {expSuperclasses = scs', expMethods = ms'}
     MethodSelectE {expArg = e} -> do
       e' <- pevalExp e
       return $ expression {expArg = e'} -}

pevalFun :: RFun -> PEval RFun
pevalFun f = do
  body <- pevalExp $ funBody f
  return $ f {funBody = body}

pevalDef :: RDef -> PEval RDef
pevalDef (Def v f) = do
  f' <- pevalFun f
  return $ Def v f'

-------------------------------------------------------------------------------
-- Dead code elimination

newtype SetUnion a = SetUnion {setUnion :: Set a}

instance Ord a => Monoid (SetUnion a) where
    mempty = SetUnion (Set.empty)
    mappend s t = SetUnion $ setUnion s `Set.union` setUnion t
    mconcat xs = SetUnion $ Set.unions $ map setUnion xs

onSetUnion :: (Set a -> Set a) -> SetUnion a -> SetUnion a
onSetUnion f (SetUnion s) = SetUnion (f s)

-- | One-pass dead code elimination.  Eliminate variables that are assigned
-- but not used.
elimDeadCode :: RDef -> RDef
elimDeadCode def = evalEDC edcDef def

-- | Dead code elimination on a value produces a new value and a set of
-- all variable names referenced by the value.
type EDC a = a -> GetMentionsSet a
type GetMentionsSet a = Writer (SetUnion Var) a

evalEDC :: EDC a -> a -> a
evalEDC f x = case runWriter $ f x of (x', _) -> x'

-- | Mention a variable.  This prevents the assignment of this variable from
-- being eliminated.
mention :: Var -> GetMentionsSet ()
mention v = tell (SetUnion $ Set.singleton v)

-- | Filter out a mention of a variable.  The variable will not appear in
-- the returned mentions set.
mask :: Var -> GetMentionsSet a -> GetMentionsSet a
mask v m = pass $ do x <- m
                     return (x, onSetUnion $ Set.delete v)

-- | Filter out a mention of a variable, and also check whether the variable
-- is mentioned.  Return True if the variable is mentioned.
maskAndCheck :: Var -> GetMentionsSet a -> GetMentionsSet (Bool, a)
maskAndCheck v m = pass $ do
  (x, mentions_set) <- listen m
  return ( (v `Set.member` setUnion mentions_set, x)
         , onSetUnion $ Set.delete v)

maskSet :: Set Var -> GetMentionsSet a -> GetMentionsSet a
maskSet vs m = pass $ do x <- m
                         return (x, onSetUnion (`Set.difference` vs))

-- | Mention all variables in a type.
edcScanType :: TypeOf Rec Rec -> GetMentionsSet ()
edcScanType t = scanType t >> return ()
  where
    scanType :: Gluon.RExp 
             -> GetMentionsSet (Gluon.RecExp Gluon.TrivialStructure)
    scanType expression =
      case expression
      of -- Scan the body of lambda/function type expressions, then delete
         -- the bound variable from the set
         Gluon.LamE { Gluon.expParam = Gluon.Binder v ty ()
                    , Gluon.expBody = b} -> do
           scanType ty
           mask v $ scanType b
         Gluon.FunE { Gluon.expMParam = Gluon.Binder' v ty ()
                    , Gluon.expRange = b} -> do
           scanType ty
           maybe id mask v $ scanType b

         -- Mention variables
         Gluon.VarE {Gluon.expVar = v} -> do
           mention v
           return Gluon.TrivialExp

         -- Recurse on other expressions
         _ -> do (Gluon.traverseExp scanType scanTuple scanProd expression
                    :: GetMentionsSet (Gluon.Exp Gluon.TrivialStructure))
                 return Gluon.TrivialExp

    scanTuple :: Gluon.RTuple
              -> GetMentionsSet (Gluon.RecTuple Gluon.TrivialStructure)
    scanTuple t =
      case t
      of Gluon.Binder' v ty val Gluon.:&: b -> do
           scanType ty
           scanType val
           maybe id mask v $ scanTuple b
         Gluon.Nil -> return Gluon.TrivialTuple

    scanProd :: Gluon.RSum
             -> GetMentionsSet (Gluon.RecSum Gluon.TrivialStructure)
    scanProd p =
      case p
      of Gluon.Binder' v ty () Gluon.:*: b -> do
           scanType ty
           maybe id mask v $ scanProd b
         Gluon.Unit -> return Gluon.TrivialSum

-- | Run the computation in a scope where the pattern is bound.
-- Return a new pattern and the result of the computation.
edcMaskPat :: RPat -> GetMentionsSet a -> GetMentionsSet (RPat, a)
edcMaskPat pat m =
  case pat
  of WildP t -> do
       edcScanType t
       x <- m
       return (pat, x)
     VarP v t -> do
       edcScanType t
       (mentioned, x) <- maskAndCheck v m

       -- If not mentioned, replace this pattern with a wildcard
       let new_pat = if mentioned then pat else WildP t
       return (new_pat, x)
     TupleP ps -> do
       (pats', x) <- edcMaskPats ps m

       -- If all patterns are wildcards, then use a single wildcard pattern
       let new_pat = if all isWildcard pats'
                     then let con = getPyonTupleType' (length pats')
                              ty = Gluon.mkInternalConAppE con $
                                   map wildcardType pats'
                          in WildP ty
                     else TupleP pats'
       return (new_pat, x)
  where
    isWildcard (WildP _) = True
    isWildcard _ = False

    wildcardType (WildP t) = t
    wildcardType _ = error "Not a wildcard pattern"

edcMaskPats :: [RPat] -> GetMentionsSet a -> GetMentionsSet ([RPat], a)
edcMaskPats (pat:pats) m = do
  (pat', (pats', x)) <- edcMaskPat pat $ edcMaskPats pats m
  return (pat':pats', x)

edcMaskPats [] m = do x <- m
                      return ([], x)

edcMaskTyPat :: RTyPat -> GetMentionsSet a -> GetMentionsSet (RTyPat, a)
edcMaskTyPat pat@(TyPat v ty) m = do
  edcScanType ty
  x <- mask v m
  return (pat, x)

edcMaskTyPats :: [RTyPat] -> GetMentionsSet a -> GetMentionsSet ([RTyPat], a)
edcMaskTyPats (pat:pats) m = do
  (pat', (pats', x)) <- edcMaskTyPat pat $ edcMaskTyPats pats m
  return (pat':pats', x)

edcMaskTyPats [] m = do x <- m
                        return ([], x)

edcDef :: EDC RDef
edcDef (Def v f) = do
  f' <- edcFun f
  return $ Def v f'

edcFun :: EDC RFun
edcFun function@(Fun { funTyParams = tps
                     , funParams = ps
                     , funReturnType = return_type
                     , funBody = body
                     }) = do
  (tps', (ps', b')) <-
    edcMaskTyPats tps $
    edcMaskPats ps $ do
      edcScanType return_type
      edcExp body
  return $ function {funTyParams = tps', funParams = ps', funBody = b'}

edcExp :: EDC RExp
edcExp expression =
  case expression
  of VarE {expVar = v} ->
       mention v >> return expression
     ConE {expCon = c} ->
       return expression
     LitE {expType = t} -> do
       edcScanType t
       return expression
     UndefinedE {expType = t} -> do
       edcScanType t
       return expression
     TupleE {expFields = fs} -> do
       fs' <- mapM edcExp fs
       return $ expression {expFields = fs'}
     TyAppE {expOper = op, expTyArg = arg} -> do
       op' <- edcExp op
       edcScanType arg
       return $ expression {expOper = op'}
     CallE {expOper = op, expArgs = args} -> do
       op' <- edcExp op
       args' <- mapM edcExp args
       return $ expression {expOper = op', expArgs = args'}
     IfE {expCond = e1, expTrueCase = e2, expFalseCase = e3} -> do
       e1' <- edcExp e1
       e2' <- edcExp e2
       e3' <- edcExp e3
       return $ expression { expCond = e1'
                           , expTrueCase = e2'
                           , expFalseCase = e3'}
     FunE {expFun = f} -> do
       f' <- edcFun f
       return $ expression {expFun = f'}
     LetE {expInfo = info, expBinder = p, expValue = e1, expBody = e2} ->
       edcLetE info p e1 e2
     LetrecE {expDefs = ds, expBody = e} ->
       maskSet (Set.fromList [v | Def v _ <- ds]) $ do
         ds' <- mapM edcDef ds
         e' <- edcExp e
         return $ expression {expDefs = ds', expBody = e'}
{-     DictE {expType = t, expSuperclasses = scs, expMethods = ms} -> do
       edcScanType t
       scs' <- mapM edcExp scs
       ms' <- mapM edcExp ms
       return $ expression {expSuperclasses = scs', expMethods = ms'}
     MethodSelectE {expType = t, expArg = e} -> do
       edcScanType t
       e' <- edcExp e
       return $ expression {expArg = e'} -}

-- | Dead code elimination for a \"let\" expression
edcLetE :: ExpInfo -> RPat -> RExp -> RExp -> GetMentionsSet RExp
edcLetE info lhs rhs body =
  -- Replace the pattern "let x = foobar in x" with "foobar"
  case body
  of VarE {expVar = v} ->
       case lhs
       of VarP v2 _ | v == v2 -> edcExp rhs
          _ -> dce_let
     _ -> dce_let
  where
    dce_let = do
      -- Structural recursion.  Try to eliminate some or all of the
      -- pattern-bound variables using knowledge of what variables are
      -- referenced in the expression body.
      (lhs', body') <- edcMaskPat lhs $ edcExp body
      rhs' <- edcExp rhs

      -- Decompose/eliminate bindings.
      return $ reconstruct_let body' $ eliminate_bindings lhs' rhs'

    -- Given a list of bindings, create some let expressions
    reconstruct_let body bindings = foldr make_let body bindings
      where
        make_let (lhs, rhs) body =
          LetE { expInfo = info
               , expBinder = lhs
               , expValue = rhs
               , expBody = body}

    -- Given the pattern and expression from a let-binding, decompose it into
    -- simpler let-bindings.  Discard unused bindings.
    --
    -- For example,
    --
    -- > let (_, a, (_, b)) = (1, foo(), (3, 4)) in ...
    --
    -- becomes
    --
    -- > let a = foo() in let b = 4 in ...
    eliminate_bindings lhs body =
      case lhs
      of -- If a side-effect-free value is not bound to anything,
         -- then this code can be eliminated.
         WildP _ | isValueExp body -> []
         TupleP ps ->
           -- If the body is a tuple expression, then decompose this into
           -- a sequence of let-bindings.
           case body
           of TupleE {expFields = es} ->
                concat $ zipWith eliminate_bindings ps es
              _ -> [(lhs, body)] 
         -- Otherwise, no change
         _ -> [(lhs, body)]