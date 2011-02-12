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

import Control.Monad.Reader
import Control.Monad.Writer
import qualified Data.IntSet as IntSet
import Data.IntSet(IntSet)
import Data.Maybe

import Common.SourcePos
import Common.Error
import Builtins.Builtins
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.DeadCode
import SystemF.Floating(floatedParameters')
import Type.Eval
import Type.Environment
import Type.Type
import Globals
import GlobalVar

-- | Locally eliminate dead code.  Top-level bindings are not eliminated.
eliminateLocalDeadCode :: Module Mem -> IO (Module Mem)
eliminateLocalDeadCode (Module module_name defss exports) = do
  tenv <- readInitGlobalVarIO the_memTypes
  let defss' = map (fmap (evalEDC tenv edcDef)) defss
      exports' = map (evalEDC tenv edcExport) exports
  return $ Module module_name defss' exports'

-- | One-pass dead code elimination.  Eliminate variables that are assigned
-- but not used.
eliminateDeadCode :: Module Mem -> IO (Module Mem)
eliminateDeadCode (Module module_name defss exports) = do
  tenv <- readInitGlobalVarIO the_memTypes
  let (defss', exports') = evalEDC tenv edcTopLevelGroup defss
  return $ Module module_name (concat defss') exports'
  where
    edcTopLevelGroup (ds:dss) = do
      (ds', (dss', exports')) <- edcDefGroup ds $ edcTopLevelGroup dss
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
  of MemWildP {} -> do
       edcType $ patMType pat
       x <- m
       return (pat, x)
     MemVarP {} -> do
       edcType $ patMType pat
       (mentioned, x) <- maskAndCheck (patMVar' pat) m

       -- If not mentioned, replace this pattern with a wildcard
       let new_pat =
             case mentioned
             of Nothing -> memWildP (patMParamType pat)
                Just u  -> setPatMUses u pat
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

-- | Eliminate dead code in a definition group and partition the group into
--   strongly-connected components.
edcDefGroup :: DefGroup (Def Mem)
            -> GetMentionsSet a
            -> GetMentionsSet ([DefGroup (Def Mem)], a)
edcDefGroup defgroup m =
  case defgroup
  of NonRec def -> do
       -- Eliminate dead code.  Decide whether the definition is dead.
       def' <- edcDef def
       (mentioned, x) <- maskAndCheck (case def of Def v _ -> v) m
       return $! if isJust mentioned
                 then ([NonRec def'], x)
                 else ([], x)
     Rec defs ->
       let local_vars = [v | Def v _ <- defs]
       in masks (mentionsSet local_vars) $ do
         -- Eliminate dead code and find references to the local variables
         defs_and_uses <- mapM (listen . edcDef) defs
         (x, MSet m_uses) <- listen m

         -- Partition into strongly connected components
         let members = [(new_def, varID v, mentions_set)
                       | (Def v _, (new_def, MSet mentions_set)) <-
                           zip defs defs_and_uses]
             new_defs = partitionDefGroup members m_uses
         return (new_defs, x)

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
     AppE {expInfo = inf, expOper = op, expTyArgs = ts, expArgs = args} ->
       edcAppE inf op ts args
     LamE {expFun = f} -> do
       f' <- edcFun f
       return $ ExpM $ base_expression {expFun = f'}
     LetE {expInfo = info, expBinder = p, expValue = e1, expBody = e2} ->
       edcLetE info p e1 e2
     LetfunE {expInfo = info, expDefs = defgroup, expBody = e} -> do
       (defgroup', e') <- edcDefGroup defgroup (edcExp e)
       return $ foldr (make_letfun info) e' defgroup'
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
  where
    make_letfun info dg e = ExpM $ LetfunE info dg e

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

-- | Dead code elimination for function application.
--
--   Perform dead code elimination on subexpressions as usual.
--   However, we use a special rule for marking uses when the operator is
--   a data constructor.  If an operand is a variable, and its representation
--   in the data constructor is 'Value' or 'Boxed', then the occurrence
--   behaves like multiple references.  We do this
--   because we do not want the value to be inlined in the simplifier.
edcAppE inf op ty_args args = do
  op' <- edcExp op
  args' <- mapM edcExp args
  tenv <- ask
  add_datacon_uses tenv op' args'
  return $ ExpM $ AppE inf op' ty_args args'
  where
    -- Determine which parameters should be floated.
    -- If a parameter should be floated, mark it as having multiple uses
    -- so it won't get inlined.
    floated_parameters tenv op' =
      case op'
      of ExpM (VarE _ op_var) -> Just $ floatedParameters' tenv op_var ty_args
         _ -> Nothing

    -- If an argument is a variable and should be floated,
    -- mark the argument as being used many times.
    add_datacon_uses tenv op' edc_args =
      case floated_parameters tenv op'
      of Nothing -> return ()
         Just floated_params ->
           mapM_ mentionMany $ 
           [v | (ExpM (VarE _ v), True) <- zip edc_args floated_params]

-- | Dead code elimination for a \"let\" expression.
--
--   The only purpose of the RHS is to assign/initialize the let-bound 
--   variable.  If the variable is not used, then remove the RHS.
edcLetE :: ExpInfo -> PatM -> ExpM -> ExpM -> GetMentionsSet ExpM
edcLetE info binder rhs body = do
  -- Scan the body and find out if it references the bound variable
  (is_live, body') <- maskAndCheck (patMVar' binder) $ edcExp body
  case is_live of
    Nothing -> return body'           -- RHS is eliminated
    Just uses -> do
      -- Must also mask the RHS, since it could mention the local variable
      rhs' <- mask (patMVar' binder) $ edcExp rhs
      binder' <- elim_dead_code_in_binder
      return $ ExpM $ LetE info (setPatMUses uses binder') rhs' body'
  where
    elim_dead_code_in_binder =
      case binder
      of MemVarP {} -> do
           edcType $ patMType binder
           return binder
         LocalVarP v ty dict uses -> do
           dict' <- edcExp dict
           edcType $ patMType binder
           return $ LocalVarP v ty dict' uses
         MemWildP {} -> internalError "edcLetE"
