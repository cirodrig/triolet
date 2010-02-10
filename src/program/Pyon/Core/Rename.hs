{- This is a temporary module while we separate statements from core syntax.
-}

{-# LANGUAGE CPP,
             TypeSynonymInstances,
             FlexibleContexts,
             TypeFamilies #-}
module Pyon.Core.Rename()
where

import Gluon.Common.Error
import Gluon.Common.Supply
import Gluon.Core.Syntax
import Gluon.Core.RenameBase
import Gluon.Core.Rename

import Pyon.Core.Syntax

-- Constraints for the expression component of a syntax to be recursive
#define RecursiveSyntax(syn) \
        Syntax syn, \
        Exp syn ~ ExpOf syn, \
        Tuple syn ~ TupOf syn, \
        Prod syn ~ ProdOf syn

instance PyonSyntax syn => PyonSyntax (SubstT syn) where
    type StmtOf (SubstT syn) = InSubstitution syn (StmtOf syn)
    type StreamOf (SubstT syn) = InSubstitution syn (StreamOf syn)
    type ProcOf (SubstT syn) = InSubstitution syn (ProcOf syn)

mapValueSubstitution :: (InSubstitution syn (ExpOf a) -> ExpOf b)
                     -> (InSubstitution syn (ProcOf a) -> ProcOf b)
                     -> InSubstitution syn (Value a) -> Value b
mapValueSubstitution e p (sub :@ val) =
    case val
    of PureVal pos x -> PureVal pos $ e (sub :@ x)
       ProcVal pos x -> ProcVal pos $ p (sub :@ x)

traverseValueSubstitution :: Monad m =>
                             (InSubstitution syn (ExpOf a) -> m (ExpOf b))
                          -> (InSubstitution syn (ProcOf a) -> m (ProcOf b))
                          -> InSubstitution syn (Value a) -> m (Value b)
traverseValueSubstitution e p (sub :@ val) =
    case val
    of PureVal pos x -> do x' <- e (sub :@ x)
                           return $ PureVal pos x'
       ProcVal pos x -> do x' <- p (sub :@ x)
                           return $ ProcVal pos x'

instance Substitutable Core Value where
    renameHead = mapValueSubstitution id id
    renameFully = mapValueSubstitution renameFully renameFully
    freshenHead = traverseValueSubstitution return return
    freshenFully = traverseValueSubstitution freshenFully freshenFully

instance Substitutable Core Stmt where
    renameHead (sub :@ stmt) =
        let r = (sub :@)
        in case stmt
           of ReturnS info val       -> ReturnS info (value val)
              CallS info v vs        -> CallS info (value v) (map value vs)
              BindS info v ante post -> BindS info v (r ante) (r post)
              CaseS info val alts    -> CaseS info (r val) (renameAlts alts)
              LetS info v val s      -> LetS info v (r val) (r s)
              LetrecS info ps v s    -> LetrecS info (renameProcs ps) v (r s)
        where
          value v = mapValue (sub :@) (sub :@) v

          renameProcs ps = map renameProc ps
          renameProc (ProcDef info v p) = ProcDef info v (sub :@ p)

          renameAlts alts = map renameAlt alts
          renameAlt (Alt info pat body) = Alt info (renamePat pat) (sub :@ body)

          renamePat (ConP con vars) = ConP con vars
          renamePat (TupP fs)       = TupP $ renameFields fs
          renamePat DefaultP        = DefaultP

          renameFields (ProdP patVar (Binder' mv ty ()) rest) =
              ProdP patVar (Binder' mv (sub :@ ty) ()) (renameFields rest)

          renameFields UnitP = UnitP

    renameFully s = mapStmt renameFully renameFully renameFully $ renameHead s

    freshenHead x = applySubstitutionT subst x
        where
          subst stmt =
              case stmt
              of ReturnS info val -> do
                   val' <- suspendValue val
                   return $ ReturnS info val'
                 CallS info v vs -> do
                   v' <- suspendValue v
                   vs' <- mapM suspendValue vs
                   return $ CallS info v' vs'
                 BindS info v ante post -> do
                   ante' <- suspend ante
                   v' <- freshenVar v
                   post' <- suspend post
                   return $ BindS info v' ante' post'
                 CaseS info val alts -> do
                   val' <- suspend val
                   alts' <- mapM (local . freshenAlt) alts
                   return $ CaseS info val' alts'
                 LetS info v val body -> do
                   val' <- suspend val
                   v' <- freshenVar v
                   body' <- suspend body
                   return $ LetS info v' val' body'
                 LetrecS info procs v body -> do
                   -- Rename all procedures and the scope variable
                   v' <- freshenVar v
                   procs' <- mapM freshenProcName procs

                   -- Then apply the renaming to the local procedures and body
                   procs'' <- mapM suspendProcDef procs'
                   body' <- suspend body
                   return $ LetrecS info procs'' v' body'

          suspendValue v =
              traverseValue suspend suspend v

    freshenFully c = traverseStmt freshenFully freshenFully freshenFully
                     =<< freshenHead c

freshenAlt :: (Supplies m VarID, RecursiveSyntax(syn)) =>
              Alt syn -> SubstitutionT syn m (Alt (SubstT syn))
freshenAlt (Alt info pat body) = do
  pat' <- freshenPat pat
  body' <- suspend body
  return $ Alt info pat' body'
    where
      freshenPat (ConP con vars) = do
        vars' <- mapM freshenConParamPat vars
        return $ ConP con vars'
          where
            freshenConParamPat RigidP = return RigidP
            freshenConParamPat (FlexibleP v) = do
              v' <- freshenVar v
              return $ FlexibleP v'

      -- In tuple patterns, locally bound variables are renamed using a
      -- separate substitution; this substitution is not visible outside the
      -- tuple.
      freshenPat (TupP fs) = do
        -- Rename local variables, then pattern-bound variables
        fs1 <- local $ renameLocalVars fs
        fs2 <- renamePatternVars fs1
        return $ TupP fs2
          where
            renameLocalVars (ProdP patVar binder fs) = do
              binder' <- freshenBinder' binder
              fs' <- renameLocalVars fs
              return $ (patVar, binder') : fs'

            renameLocalVars UnitP = return []

            renamePatternVars ((patVar, binder) : fs) = do
              patVar' <- freshenVar patVar
              fs' <- renamePatternVars fs
              return $ ProdP patVar' binder fs'

            renamePatternVars [] = return UnitP

      freshenPat DefaultP = return DefaultP

-- To deal with recursive procedures, we split freshening into two parts.
-- The first part only renames bound variables and updates a substitution.
-- Once all renamings are in the substitution, we go ahead with the second
-- part, which is applying the renaming to the entire procedure.

-- Reassign a procedure's bound variable
freshenProcName procDef = do
  v' <- freshenVar (procName procDef)
  return $ procDef {procName = v'}

-- Reassign a procedure's fields, but leave the bound variable unchanged.
suspendProcDef :: (Monad m, Supplies m VarID) =>
                  ProcDef syn -> SubstitutionT syn m (ProcDef (SubstT syn))
suspendProcDef (ProcDef info name proc) = do
  proc' <- suspend proc
  return $ ProcDef info name proc'

instance Substitutable Core Stream where
    renameHead (sub :@ str) =
        case str
        of DoR info stmt -> DoR info (sub :@ stmt)
           CallR info v vs -> CallR info (value v) (map value vs)
        where
          value = mapValue (sub :@) (sub :@)

    renameFully e = mapStream renameFully renameFully renameFully $
                    renameHead e

    freshenHead x = applySubstitutionT subst x
        where
          subst str =
              case str
              of DoR info stmt -> do
                   stmt' <- suspend stmt
                   return $ DoR info stmt'
                 CallR info v vs -> do
                   v' <- traverseValue suspend suspend v
                   vs' <- mapM (traverseValue suspend suspend) vs
                   return $ CallR info v' vs'

    freshenFully e = traverseStream freshenFully freshenFully freshenFully =<<
                     freshenHead e

instance Substitutable Core Proc where
    renameHead (sub :@ proc) =
        let r      = (sub :@)
            params = map (mapBinder id r) (procParams proc)
            ret    = r (procReturn proc)
            eff    = r (procEffect proc)
            bodyStmt = r (procBodyStmt proc)
            bodyStr = r (procBodyStream proc)
        in if isStmtProc proc
           then Proc params ret eff bodyStmt
           else Producer params ret eff bodyStr

    renameFully p = mapProc renameFully renameFully $ renameHead p

    freshenHead x = applySubstitutionT subst x
        where
          subst proc = do
            binders <- mapM freshenBinderInvariant (procParams proc)
            ret <- suspend $ procReturn proc
            eff <- suspend $ procEffect proc
            if isStmtProc proc
              then do body <- suspend $ procBodyStmt proc
                      return $ Proc binders ret eff body
              else do body <- suspend $ procBodyStream proc 
                      return $ Producer binders ret eff body

    freshenFully p = traverseProc freshenFully freshenFully =<< freshenHead p
