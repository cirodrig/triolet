{-| Memory-level dead code elimination. 
--
-- This module does two important things.
-- It eliminates redundant let-bindings, and it converts
-- unused pattern bindings to wildcards.
--
-- Wildcard pattern bindings facilitate elimination of case statements.
-}

module SystemF.DeadCodeMem(eliminateLocalDeadCode, eliminateDeadCode)
where

import Control.Monad.Writer
import qualified Data.Set as Set
import Data.Set(Set)

import Common.SourcePos
import Common.Error
import Builtins.Builtins
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.DeadCode
import Type.Type

-- | Locally eliminate dead code.  Top-level bindings are not eliminated.
eliminateLocalDeadCode :: Module Mem -> Module Mem
eliminateLocalDeadCode (Module module_name defss exports) =
  let defss' = map (map (evalEDC edcDef)) defss
      exports' = map (evalEDC edcExport) exports
  in Module module_name defss' exports'

-- | One-pass dead code elimination.  Eliminate variables that are assigned
-- but not used.
eliminateDeadCode :: Module Mem -> Module Mem
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

-------------------------------------------------------------------------------

-- | Mention all variables in a type
edcScanType :: TypM -> GetMentionsSet ()
edcScanType (TypM t) = edcType t

-- | Find mentioned variables in an export declaration
edcExport :: Export Mem -> GetMentionsSet (Export Mem)
edcExport export = do
  fun <- edcFun $ exportFunction export
  return $ export {exportFunction = fun}

-- | Run the computation in a scope where the pattern is bound.
--   Return a new pattern and the result of the computation.
edcMaskPat :: PatM -> GetMentionsSet a -> GetMentionsSet (PatM, a)
edcMaskPat pat m =
  case pat
  of MemWildP (_ ::: t) -> do
       edcType t
       x <- m
       return (pat, x)
     MemVarP v ptype@(_ ::: t) -> do
       edcType t
       (mentioned, x) <- maskAndCheck v m

       -- If not mentioned, replace this pattern with a wildcard
       let new_pat = if mentioned then pat else MemWildP ptype
       return (new_pat, x)
     LocalVarP {} -> internalError "edcMaskPat"

edcMaskPats :: [PatM] -> GetMentionsSet a -> GetMentionsSet ([PatM], a)
edcMaskPats (pat:pats) m = do
  (pat', (pats', x)) <- edcMaskPat pat $ edcMaskPats pats m
  return (pat':pats', x)

edcMaskPats [] m = do x <- m
                      return ([], x)

edcMaskTyPat :: TyPatM -> GetMentionsSet a -> GetMentionsSet (TyPatM, a)
edcMaskTyPat pat@(TyPatM v ty) m = do
  edcType ty
  x <- mask v m
  return (pat, x)

edcMaskTyPats :: [TyPatM] -> GetMentionsSet a -> GetMentionsSet ([TyPatM], a)
edcMaskTyPats (pat:pats) m = do
  (pat', (pats', x)) <- edcMaskTyPat pat $ edcMaskTyPats pats m
  return (pat':pats', x)

edcMaskTyPats [] m = do x <- m
                        return ([], x)

edcDef :: EDC (Def Mem)
edcDef (Def v f) = do
  f' <- edcFun f
  return $ Def v f'

edcFun :: EDC FunM
edcFun (FunM function@(Fun { funTyParams = tps
                           , funParams = ps
                           , funReturn = RetM (_ ::: return_type)
                           , funBody = body
                           })) = do
  -- Eliminate dead code and convert patterns to wildcard patterns.
  (tps', (ps', b')) <-
    edcMaskTyPats tps $
    edcMaskPats ps $ do
      edcType return_type
      edcExp body
  return $ FunM $ function {funTyParams = tps', funParams = ps', funBody = b'}

edcExp :: EDC ExpM
edcExp expression@(ExpM base_expression) =
  case base_expression
  of VarE {expVar = v} ->
       mention v >> return expression
     LitE {} ->
       return expression
     AppE {expOper = op, expArgs = args} -> do
       -- Type arguments don't change
       op' <- edcExp op
       args' <- mapM edcExp args
       return $ ExpM $ base_expression {expOper = op', expArgs = args'}
     LamE {expFun = f} -> do
       f' <- edcFun f
       return $ ExpM $ base_expression {expFun = f'}
     LetE {expInfo = info, expBinder = p, expValue = e1, expBody = e2} ->
       edcLetE info p e1 e2
     LetrecE {expDefs = ds, expBody = e} ->
       masks (Set.fromList [varID v | Def v _ <- ds]) $ do
         ds' <- mapM edcDef ds
         e' <- edcExp e
         return $ ExpM $ base_expression {expDefs = ds', expBody = e'}
     CaseE {expInfo = inf, expScrutinee = scr, expAlternatives = alts} -> do
       scr' <- edcExp scr
       alts' <- mapM edcAlt alts
       case alts' of
         [alt'] | null (altExTypes $ fromAltM alt') &&
                  all isWildPatM (altParams $ fromAltM alt') ->
           -- This case statement has no effect
           return (altBody $ fromAltM alt')
         _ -> 
           return $ ExpM $ CaseE { expInfo = inf
                                 , expScrutinee = scr'
                                 , expAlternatives = alts'}

isWildPatM (MemWildP {}) = True
isWildPatM _ = False

-- | Dead code elimination for a case alternative
edcAlt (AltM alt) = do
  mapM_ edcScanType $ altTyArgs alt
  -- Mask out variables bound by the alternative and simplify the body
  (typats, (pats, body)) <-
    edcMaskTyPats (altExTypes alt) $
    edcMaskPats (altParams alt) $
    edcExp (altBody alt)
  
  return $ AltM $ Alt { altConstructor = altConstructor alt 
                      , altTyArgs = altTyArgs alt
                      , altExTypes = typats
                      , altParams = pats
                      , altBody = body}

-- | Dead code elimination for a \"let\" expression.
--
--   The only purpose of the RHS is to assign/initialize the let-bound 
--   variable.  If the variable is not used, then remove the RHS.
edcLetE :: ExpInfo -> PatM -> ExpM -> ExpM -> GetMentionsSet ExpM
edcLetE info binder rhs body = do
  -- Scan the body and find out if it references the bound variable
  (is_live, body') <- maskAndCheck (patMVar' binder) $ edcExp body
  if not is_live
    then return body'           -- RHS is eliminated
    else do
      -- Must also mask the RHS, since it could mention the local variable
      rhs' <- mask (patMVar' binder) $ edcExp rhs
      binder' <- elim_dead_code_in_binder
      return $ ExpM $ LetE info binder' rhs' body'
  where
    elim_dead_code_in_binder =
      case binder
      of MemVarP v (_ ::: ty) -> do
           edcType ty
           return binder
         LocalVarP v ty dict -> do
           dict' <- edcExp dict
           edcType ty
           return $ LocalVarP v ty dict'
         MemWildP {} -> internalError "edcLetE"
