-- | Partial evaluation.
-- This module collects several ways of simplifying Pyon code through a 
-- sort of compile-time execution.  Copy propagation, constant propagation,
-- constant folding, and case elimination are performed this way.  Partial
-- evaluation maintains an \"execution environment\" of local variable
-- assignments.

{-# LANGUAGE ViewPatterns #-}
module Pyon.SystemF.PartialEval(partialEvaluateModule)
where

import Control.Monad.Reader
import Data.List
import qualified Data.Map as Map

import Gluon.Common.SourcePos
import Gluon.Common.Error
import Gluon.Core(mkSynInfo, Level(..))
import Pyon.SystemF.Builtins
import Pyon.SystemF.Syntax

catEndo :: [a -> a] -> a -> a
catEndo fs x = foldr ($) x fs

-- | The 'PE' monad holds the current variable-to-value assignment.
type PE a = Reader (Map.Map Var RExp) a

runPE m = runReader m Map.empty

-- | Look up the value of a variable
lookupVar :: Var -> PE (Maybe RExp)
lookupVar v = asks (Map.lookup v)

-- | Look up the value of a variable; supply a default value if none
-- is available
lookupVarDefault :: RExp -> Var -> PE RExp
lookupVarDefault defl v = asks (Map.findWithDefault defl v)

-- | If the expression is a tuple expression, then return the expression's
-- field values.
deconstructTupleExp :: RExp -> Maybe [RExp]
deconstructTupleExp expression =
  -- If the operator is a tuple value constructor, then return the arguments
  -- otherwise, return nothing
  case unpackPolymorphicCall expression
  of Just (ConE {expCon = con}, ty_args, args)
       | Just con == getPyonTupleCon (length args) -> Just args
     _ -> Nothing

-- | Given a value and the pattern it is bound to, add the bound value(s)
-- to the environment.  The caller should verify that the value has no
-- side effects.  Any values that cannot be added to the environment will be
-- ignored.
bindValue :: RPat -> RExp -> PE a -> PE a
bindValue (WildP _)   _ m = m
bindValue (VarP v t)  e m = local (Map.insert v e) m
bindValue (TupleP ps) e m = 
  case deconstructTupleExp e
  of Nothing -> m               -- Cannot bind this value 
     Just es -> catEndo (zipWith bindValue ps es) m

-------------------------------------------------------------------------------

partialEvaluateModule :: RModule -> RModule
partialEvaluateModule (Module defss exports) =
  let defss' = runPE (pevalDefGroups defss)
  in Module defss' exports

pevalDefGroups :: [DefGroup Rec] -> PE [DefGroup Rec]
pevalDefGroups (defs:defss) =
  liftM (uncurry (:)) $ pevalDefGroup defs $ pevalDefGroups defss

pevalDefGroups [] = return []

pevalDefGroup :: DefGroup Rec -> PE a -> PE (DefGroup Rec, a)
pevalDefGroup dg m = do
  dg' <- mapM pevalDef dg
  x <- m
  return (dg', x)

pevalDef :: RDef -> PE RDef
pevalDef (Def v f) = do
  f' <- pevalFun f
  return $ Def v f'

pevalFun :: RFun -> PE RFun
pevalFun f = do
  body <- pevalExp $ funBody f
  return $ f {funBody = body}

-- | Partial evaluation of an expression.
pevalExp :: RExp -> PE RExp

-- Function call evaluation
pevalExp expression@(unpackPolymorphicCall -> Just (op, ty_args, args)) = do
  -- Evaluate subexpressions
  args' <- mapM pevalExp args
  op' <- pevalExp op
  
  -- TODO: Try to statically evaluate this function
  return $ build_call op' ty_args args'
  where
    inf = expInfo expression
    
    build_call op (t:ts) args =
      let op' = TyAppE inf op t
      in build_call op' ts args
    
    build_call op [] args = CallE inf op args
  
pevalExp expression =
  case expression
  of VarE {expVar = v} -> lookupVarDefault expression v
     ConE {} -> return expression
     LitE {} -> return expression
     TyAppE {expOper = op} -> do
       op' <- pevalExp op
       return $ expression {expOper = op'}
     CallE {} -> internalError "pevalExp" -- Should have been already matched
     FunE {expFun = f} -> do
       f' <- pevalFun f
       return $ expression {expFun = f'}
     
     -- This expression is generated sometimes by SSA.
     -- Replace "let x = FOO in x" with FOO.  Continue simplifying FOO.
     LetE { expBinder = VarP v _
          , expValue = rhs
          , expBody = VarE {expVar = v'}}
       | v == v' ->
         pevalExp rhs
     LetE {expBinder = pat, expValue = rhs, expBody = body} -> do
       -- Simplify RHS
       rhs' <- pevalExp rhs
       
       -- Bind pattern and evaluate body
       body' <- bindValue pat rhs' $ pevalExp body
       
       return $ expression {expValue = rhs', expBody = body'}
       
     LetrecE {expDefs = defs, expBody = body} -> do
       (defs', body') <- pevalDefGroup defs $ pevalExp body
       
       return $ expression {expDefs = defs', expBody = body'}
     
     CaseE {expInfo = inf, expScrutinee = scr, expAlternatives = alts} -> do
       scr' <- pevalExp scr
       
       -- If possible, eliminate this case statement
       case eliminateCase (getSourcePos inf) scr' alts of
         Just e -> pevalExp e
         Nothing -> do
           alts' <- mapM pevalAlt alts
           return $ expression {expScrutinee = scr', expAlternatives = alts'}

-- | Attempt to eliminate a case statement.  If the scrutinee is a constructor
-- application and it matches an alternative, replace the case statement 
-- with the alternative.
eliminateCase :: SourcePos -> RExp -> [Alt Rec] -> Maybe RExp
eliminateCase pos scrutinee alternatives =
  -- Is the scrutinee a constructor application?
  case unpackPolymorphicCall scrutinee
  of Just (ConE {expCon = scrutinee_con}, ty_args, args) ->
       -- Find a matching alternative
       case find ((scrutinee_con ==) . altConstructor) alternatives
       of Just alt ->
            -- Assume that type arguments match, because the code passed 
            -- type checking.
            -- Bind parameters to the constructor's fields.
            Just $ foldr make_let (altBody alt) $ zip args (altParams alt)
          Nothing -> Nothing    -- No matching alternative
     _ -> Nothing               -- Cannot determine constructor of scrutinee
  where
    make_let (arg, Binder v ty ()) expr =
      LetE { expInfo = mkSynInfo pos ObjectLevel
           , expBinder = VarP v ty
           , expValue = arg
           , expBody = expr
           }

pevalAlt :: Alt Rec -> PE (Alt Rec)
pevalAlt alt = do
  body' <- pevalExp $ altBody alt
  return $ alt {altBody = body'}
  