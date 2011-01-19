
module SystemF.DeadCode(eliminateDeadCode)
where

import Control.Monad.Writer
import qualified Data.Set as Set
import Data.Set(Set)

import Gluon.Common.SourcePos
import Gluon.Common.Error
import Builtins.Builtins
import SystemF.Syntax
import Type.Type
import Type.Var

-- | One-pass dead code elimination.  Eliminate variables that are assigned
-- but not used.
eliminateDeadCode :: RModule -> RModule
eliminateDeadCode (Module module_name defss exports) =
  let (defss', exports') = evalEDC edcTopLevelGroup defss
  in Module module_name defss' exports'
  where
    edcTopLevelGroup (ds:dss) =
      masks (Set.fromList [varID v | Def v _ <- ds]) $ do
        ds' <- mapM edcDef ds
        (dss', exports') <- edcTopLevelGroup dss
        return (ds' : dss', exports')
    
    edcTopLevelGroup [] = do
      exports' <- mapM edcExport exports
      return ([], exports')

-- | If the expression is a tuple expression, then return the expression's
-- field values.
deconstructTupleExp :: RExp -> Maybe [RExp]
deconstructTupleExp expression =
  -- If the operator is a tuple value constructor, then return the arguments
  -- otherwise, return nothing
  case unpackPolymorphicCall expression
  of Just (VarE {expVar = con}, ty_args, args)
       | con == pyonTupleCon (length args) -> Just args
     _ -> Nothing

-------------------------------------------------------------------------------

-- | Sets form a monoid under the union operation
newtype Union a = Union {getUnion :: Set a}

instance Ord a => Monoid (Union a) where
    mempty = Union (Set.empty)
    mappend s t = Union $ getUnion s `Set.union` getUnion t
    mconcat xs = Union $ Set.unions $ map getUnion xs

onUnion :: (Set a -> Set a) -> Union a -> Union a
onUnion f (Union s) = Union (f s)

-- | Dead code elimination on a value produces a new value and a set of
-- all variable names referenced by the value.
type EDC a = a -> GetMentionsSet a
type GetMentionsSet a = Writer (Union VarID) a

evalEDC :: (a -> GetMentionsSet b) -> a -> b
evalEDC f x = case runWriter $ f x of (x', _) -> x'

-- | Mention a variable.  This prevents the assignment of this variable from
-- being eliminated.
mention :: Var -> GetMentionsSet ()
mention v = tell (Union $ Set.singleton (varID v))

-- | Filter out a mention of a variable.  The variable will not appear in
-- the returned mentions set.
mask :: Var -> GetMentionsSet a -> GetMentionsSet a
mask v m = pass $ do x <- m
                     return (x, onUnion $ Set.delete (varID v))

-- | Filter out a mention of a variable, and also check whether the variable
-- is mentioned.  Return True if the variable is mentioned.
maskAndCheck :: Var -> GetMentionsSet a -> GetMentionsSet (Bool, a)
maskAndCheck v m = pass $ do
  (x, mentions_set) <- listen m
  return ( (varID v `Set.member` getUnion mentions_set, x)
         , onUnion $ Set.delete (varID v))

masks :: Set VarID -> GetMentionsSet a -> GetMentionsSet a
masks vs m = pass $ do x <- m
                       return (x, onUnion (`Set.difference` vs))

-- | Mention all variables in a type
edcScanType :: RType -> GetMentionsSet ()
edcScanType (SFType t) = scanType t
  where
    scanType :: Type -> GetMentionsSet ()
    scanType (VarT v) = mention v
    scanType (AppT t1 t2) = scanType t1 >> scanType t2
    scanType (FunT (ValPT (Just v) ::: dom) (_ ::: rng)) = do
      scanType dom
      mask v $ scanType rng
    scanType (FunT (_ ::: dom) (_ ::: rng)) = do
      scanType dom
      scanType rng

-- | Find mentioned variables in an export declaration
edcExport :: Export Rec -> GetMentionsSet (Export Rec)
edcExport export = do
  fun <- edcFun $ exportFunction export
  return $ export {exportFunction = fun}

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
                     then let con = pyonTupleTypeCon (length pats')
                              ty = varApp con $ map wildcardType pats'
                          in WildP $ SFType ty
                     else TupleP pats'
       return (new_pat, x)
  where
    isWildcard (WildP _) = True
    isWildcard _ = False

    wildcardType (WildP t) = fromSFType t
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
     LitE {expType = t} -> do
       edcScanType t
       return expression
     TyAppE {expOper = op, expTyArg = arg} -> do
       op' <- edcExp op
       edcScanType arg
       return $ expression {expOper = op'}
     CallE {expOper = op, expArgs = args} -> do
       op' <- edcExp op
       args' <- mapM edcExp args
       return $ expression {expOper = op', expArgs = args'}
     FunE {expFun = f} -> do
       f' <- edcFun f
       return $ expression {expFun = f'}
     LetE {expInfo = info, expBinder = p, expValue = e1, expBody = e2} ->
       edcLetE info p e1 e2
     LetrecE {expDefs = ds, expBody = e} ->
       masks (Set.fromList [varID v | Def v _ <- ds]) $ do
         ds' <- mapM edcDef ds
         e' <- edcExp e
         return $ expression {expDefs = ds', expBody = e'}
     CaseE {expScrutinee = scr, expAlternatives = alts} -> do
       scr' <- edcExp scr
       alts' <- mapM edcAlt alts
       return $ expression {expScrutinee = scr', expAlternatives = alts'}

-- | Dead code elimination for a case alternative
edcAlt alt = do
  -- Mask out variables bound by the alternative and simplify the body
  body' <- masks (Set.fromList [varID v | VarP v _ <- altParams alt]) $ do
    edcExp (altBody alt)
  return $ alt {altBody = body'} 

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

      -- Decompose/eliminate bindings.
      let bindings = eliminate_bindings lhs' rhs

      -- Recurse in RHS.
      bindings' <- forM bindings $ \(sub_lhs, sub_rhs) -> do
        sub_rhs' <- edcExp sub_rhs
        return (sub_lhs, sub_rhs')

      -- Reconstruct the let expression
      return $ reconstruct_let body' bindings'

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
      of -- If a value is not bound to anything,
         -- then this code can be eliminated.
         WildP _ -> []
         TupleP ps -> 
           case deconstructTupleExp body
           of Nothing -> [(lhs, body)] -- Cannot deconstruct this pattern 
              Just fs -> concat $ zipWith eliminate_bindings ps fs
         -- Otherwise, no change
         _ -> [(lhs, body)]