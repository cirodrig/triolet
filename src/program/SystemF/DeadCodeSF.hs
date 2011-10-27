
module SystemF.DeadCodeSF(eliminateDeadCode)
where

import Control.Monad.Writer
import qualified Data.IntSet as IntSet
import Data.IntSet(IntSet)
import Data.Maybe

import Common.SourcePos
import Common.Error
import Builtins.Builtins
import SystemF.Syntax
import SystemF.DeadCode
import Type.Type
import Globals
import GlobalVar

-- | One-pass dead code elimination.  Eliminate variables that are assigned
-- but not used.
eliminateDeadCode :: Module SF -> IO (Module SF)
eliminateDeadCode (Module module_name [] defss exports) = do
  tenv <- readInitGlobalVarIO the_systemFTypes
  let (defss', exports') = evalEDC tenv edcTopLevelGroup defss
  return $ Module module_name [] defss' exports'
  where
    edcTopLevelGroup (ds:dss) = do
      (ds', (dss', exports')) <- edcDefGroup ds $ edcTopLevelGroup dss
      return (ds' : dss', exports')
    
    edcTopLevelGroup [] = do
      exports' <- mapM edcExport exports
      return ([], exports')

-- | If the expression is a tuple expression, then return the expression's
-- field values.
deconstructTupleExp :: ExpSF -> Maybe [ExpSF]
deconstructTupleExp expression =
  -- If the operator is a tuple value constructor, then return the arguments
  -- otherwise, return nothing
  case unpackPolymorphicCall expression
  of Just (ExpSF (VarE {expVar = con}), ty_args, args)
       | isPyonTupleCon con -> Just args
     _ -> Nothing

-------------------------------------------------------------------------------

-- | Find mentioned variables in an export declaration
edcExport :: Export SF -> GetMentionsSet (Export SF)
edcExport export = do
  fun <- edcFun $ exportFunction export
  return $ export {exportFunction = fun}

-- | Run the computation in a scope where the pattern is bound.
-- Return a new pattern and the result of the computation.
edcMaskPat :: PatSF -> GetMentionsSet a -> GetMentionsSet (PatSF, Bool, a)
edcMaskPat pat@(VarP v t) m = do
  edcType t
  (mentioned, x) <- maskAndCheck v m
  return (pat, isJust mentioned, x)

edcMaskPats :: [PatSF] -> GetMentionsSet a -> GetMentionsSet ([PatSF], a)
edcMaskPats (pat:pats) m = do
  (pat', _, (pats', x)) <- edcMaskPat pat $ edcMaskPats pats m
  return (pat':pats', x)

edcMaskPats [] m = do x <- m
                      return ([], x)

edcMaskTyPat :: TyPat -> GetMentionsSet a -> GetMentionsSet (TyPat, a)
edcMaskTyPat pat@(TyPat (v ::: ty)) m = do
  edcType ty
  x <- mask v m
  return (pat, x)

edcMaskTyPats :: [TyPat] -> GetMentionsSet a -> GetMentionsSet ([TyPat], a)
edcMaskTyPats (pat:pats) m = do
  (pat', (pats', x)) <- edcMaskTyPat pat $ edcMaskTyPats pats m
  return (pat':pats', x)

edcMaskTyPats [] m = do x <- m
                        return ([], x)

edcDef :: EDC (Def SF)
edcDef def = mapMDefiniens edcFun def

edcDefGroup :: DefGroup (Def SF)
            -> GetMentionsSet a
            -> GetMentionsSet (DefGroup (Def SF), a)
edcDefGroup defgroup m =
  case defgroup
  of NonRec def -> do
       def' <- edcDef def
       x <- mask (definiendum def) m
       return (NonRec def', x)
     Rec defs -> masks (mentionsSet $ map definiendum defs) $ do
       defs' <- mapM edcDef defs
       x <- m
       return (Rec defs', x)

edcFun :: EDC FunSF
edcFun (FunSF function@(Fun { funTyParams = tps
                            , funParams = ps
                            , funReturn = return_type
                            , funBody = body
                            })) = do
  (tps', (ps', b')) <-
    edcMaskTyPats tps $
    edcMaskPats ps $ do
      edcType return_type
      edcExp body
  return $ FunSF $ function {funTyParams = tps', funParams = ps', funBody = b'}

edcExp :: EDC ExpSF
edcExp expression@(ExpSF base_expression) =
  case base_expression
  of VarE {expVar = v} ->
       mention v >> return expression
     LitE {} ->
       return expression
     ConE {expArgs = args} -> do
       args' <- mapM edcExp args
       return $ ExpSF $ base_expression {expArgs = args'}
     AppE {expOper = op, expArgs = args} -> do
       -- Type arguments don't change
       op' <- edcExp op
       args' <- mapM edcExp args
       return $ ExpSF $ base_expression {expOper = op', expArgs = args'}
     LamE {expFun = f} -> do
       f' <- edcFun f
       return $ ExpSF $ base_expression {expFun = f'}
     LetE {expInfo = info, expBinder = p, expValue = e1, expBody = e2} ->
       edcLetE info p e1 e2
     LetfunE {expDefs = ds, expBody = e} -> do
       (ds', e') <- edcDefGroup ds $ edcExp e
       return $ ExpSF $ base_expression {expDefs = ds', expBody = e'}
     CaseE {expScrutinee = scr, expAlternatives = alts} -> do
       scr' <- edcExp scr
       alts' <- mapM edcAlt alts
       return $ ExpSF $ base_expression {expScrutinee = scr',
                                         expAlternatives = alts'}
     CoerceE inf from_t to_t body -> do
       body' <- edcExp body
       return $ ExpSF $ CoerceE inf from_t to_t body'

-- | Dead code elimination for a case alternative
edcAlt (AltSF alt) = do
  let con = altCon alt
  mapM_ edcType $ deConTyArgs con
  -- Mask out variables bound by the alternative and simplify the body
  let local_vars = [v | VarP v _ <- altParams alt] ++
                   [v | v ::: _ <- deConExTypes con]
  body' <- masks (mentionsSet local_vars) $ do
    edcExp (altBody alt)
  return $ AltSF $ alt {altBody = body'} 

-- | Dead code elimination for a \"let\" expression
edcLetE :: ExpInfo -> PatSF -> ExpSF -> ExpSF -> GetMentionsSet ExpSF
edcLetE info lhs rhs body =
  -- Replace the pattern "let x = foobar in x" with "foobar"
  case fromExpSF body
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
      (lhs', lhs_mentioned, body') <- edcMaskPat lhs $ edcExp body

      -- If LHS is not mentioned, remove the binding from the program.
      if not lhs_mentioned then return body' else do
        rhs' <- edcExp rhs
        return $ ExpSF $ LetE info lhs' rhs' body'
