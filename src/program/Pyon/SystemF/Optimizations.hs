
module Pyon.SystemF.Optimizations
    (optimizeModule)
where

import Control.Monad
import Control.Monad.Writer

import Data.Set(Set)
import qualified Data.Set as Set

import qualified Gluon.Core as Gluon
import qualified Gluon.Eval.Typecheck as Gluon
import Pyon.SystemF.Syntax

catEndo :: [a -> a] -> a -> a
catEndo fs x = foldr ($) x fs

-- | Apply optimizations to a module.
optimizeModule :: Module -> Module
optimizeModule mod =
  mapModule elimDeadCode mod

mapModule :: (Def -> Def) -> Module -> Module
mapModule f (Module ds) = Module (map f ds)

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
elimDeadCode :: Def -> Def
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

maskSet :: Set Var -> GetMentionsSet a -> GetMentionsSet a
maskSet vs m = pass $ do x <- m
                         return (x, onSetUnion (`Set.difference` vs))

-- | Mention all variables in a type.
edcScanType :: PyonType -> GetMentionsSet ()
edcScanType t = scanType t >> return ()
  where
    scanType :: Gluon.ExpOf Gluon.Core
             -> GetMentionsSet (Gluon.ExpOf Gluon.TrivialSyntax)
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
         Gluon.VarE {Gluon.expVar = v} -> mention v

         -- Recurse on other expressions
         _ -> do (Gluon.traverseExp scanType scanTuple scanProd expression
                    :: GetMentionsSet (Gluon.Exp Gluon.TrivialSyntax))
                 return ()

    scanTuple :: Gluon.TupOf Gluon.Core
              -> GetMentionsSet (Gluon.TupOf Gluon.TrivialSyntax)
    scanTuple t =
      case t
      of Gluon.Binder' v ty val Gluon.:&: b -> do
           scanType ty
           scanType val
           maybe id mask v $ scanTuple b
         Gluon.Nil -> return ()

    scanProd :: Gluon.ProdOf Gluon.Core
             -> GetMentionsSet (Gluon.ProdOf Gluon.TrivialSyntax)
    scanProd p =
      case p
      of Gluon.Binder' v ty () Gluon.:*: b -> do
           scanType ty
           maybe id mask v $ scanProd b

-- | Run the computation in a scope where the pattern is bound.
-- Return a new pattern and the result of the computation.
edcMaskPat :: Pat -> GetMentionsSet a -> GetMentionsSet (Pat, a)
edcMaskPat pat m =
  case pat
  of WildP t -> do
       edcScanType t
       x <- m
       return (pat, x)
     VarP v t -> do
       edcScanType t
       x <- mask v m
       return (pat, x)
     TupleP ps -> do
       (pats', x) <- edcMaskPats ps m
       return (TupleP pats', x)

edcMaskPats :: [Pat] -> GetMentionsSet a -> GetMentionsSet ([Pat], a)
edcMaskPats (pat:pats) m = do
  (pat', (pats', x)) <- edcMaskPat pat $ edcMaskPats pats m
  return (pat':pats', x)

edcMaskPats [] m = do x <- m
                      return ([], x)

edcMaskTyPat :: TyPat -> GetMentionsSet a -> GetMentionsSet (TyPat, a)
edcMaskTyPat pat@(TyPat v ty) m = do
  edcScanType ty
  x <- mask v m
  return (pat, x)

edcMaskTyPats :: [TyPat] -> GetMentionsSet a -> GetMentionsSet ([TyPat], a)
edcMaskTyPats (pat:pats) m = do
  (pat', (pats', x)) <- edcMaskTyPat pat $ edcMaskTyPats pats m
  return (pat':pats', x)

edcMaskTyPats [] m = do x <- m
                        return ([], x)

edcDef :: EDC Def
edcDef (Def v f) = do
  f' <- edcFun f
  return $ Def v f'

edcFun :: EDC Fun
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

edcExp :: EDC Exp
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
     LetE {expBinder = p, expValue = e1, expBody = e2} -> do
       (p', e1') <- edcMaskPat p $ edcExp e1
       e2' <- edcExp e2
       return $ expression {expBinder = p', expValue = e1', expBody = e2'}
     LetrecE {expDefs = ds, expBody = e} ->
       maskSet (Set.fromList [v | Def v _ <- ds]) $ do
         ds' <- mapM edcDef ds
         e' <- edcExp e
         return $ expression {expDefs = ds', expBody = e'}
     DictE {expType = t, expSuperclasses = scs, expMethods = ms} -> do
       edcScanType t
       scs' <- mapM edcExp scs
       ms' <- mapM edcExp ms
       return $ expression {expSuperclasses = scs', expMethods = ms'}
     MethodSelectE {expType = t, expArg = e} -> do
       edcScanType t
       e' <- edcExp e
       return $ expression {expArg = e'}
