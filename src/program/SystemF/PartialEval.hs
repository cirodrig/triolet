-- | Partial evaluation.
-- This module collects several ways of simplifying Pyon code through a
-- sort of compile-time execution.  Copy propagation, constant propagation,
-- constant folding, un-currying, and case elimination are performed this way.
-- Partial evaluation maintains an \"execution environment\" of local variable
-- assignments.

{-# LANGUAGE ViewPatterns #-}
module SystemF.PartialEval(partialEvaluateModule)
where

import Control.Monad.Reader
import Data.List
import qualified Data.Map as Map
import Data.Maybe

import Gluon.Common.SourcePos
import Gluon.Common.Error
import Gluon.Core(mkSynInfo)
import Gluon.Core.Level
import Builtins.Builtins
import SystemF.Syntax
import Type.Var
import Type.Type

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
  case uncurryUnpackPolymorphicCall expression
  of Just (VarE {expVar = con}, ty_args, args)
       | con == pyonTupleCon (length args) -> Just args
     _ -> Nothing

-- | Uncurry a function call.
--
-- Transform nested calls of the form @((f x y) z w)@ into flat calls
-- of the form @(f x y z w)@.
uncurryCall :: RExp -> RExp
uncurryCall op = fromMaybe op $ uncurryCall' op

-- | Uncurry a function call.  Return 'Nothing' if nothing changes.
uncurryCall' (CallE {expInfo = inf, expOper = op, expArgs = args}) =
  case uncurryCall op
  of CallE {expOper = op', expArgs = args'} ->
       Just $ CallE {expInfo = inf, expOper = op', expArgs = args' ++ args}
     _ -> Nothing

uncurryCall' _ = Nothing

-- | Uncurry and unpack a polymorphic function call.
uncurryUnpackPolymorphicCall e = unpackPolymorphicCall (uncurryCall e)

-- | Unpack a polymorphic call, possibly surrounded by let-expressions.
-- Return the unpacked call and bindings.
unpackPolymorphicCallAndBindings :: RExp
                                 -> Maybe ([(ExpInfo, RPat, RExp)],
                                           RExp,
                                           [RType],
                                           [RExp])
unpackPolymorphicCallAndBindings expression =
  case expression
  of LetE { expInfo = inf
          , expBinder = pat
          , expValue = val
          , expBody = body} ->
       case unpackPolymorphicCallAndBindings body
       of Just (bindings, op, ty_args, args) ->
            Just ((inf, pat, val) : bindings, op, ty_args, args)
          Nothing -> Nothing
     _ -> case uncurryUnpackPolymorphicCall expression
          of Just (op, ty_args, args) -> Just ([], op, map SFType ty_args, args)
             Nothing -> Nothing

applyBindings :: [(ExpInfo, RPat, RExp)] -> RExp -> RExp
applyBindings bs e = foldr make_let e bs
  where
    make_let (info, pat, rhs) body =
      LetE {expInfo = info, expBinder = pat, expValue = rhs, expBody = body}

-- | Return True if the expression is \"simple\" and thus worthy of
-- inlining.  We don't want to increase the amount of work performed by
-- by evaluating the same expression repeatedly, unless it is a known-cheap
-- expression.
isSimpleExp :: RExp -> Bool
isSimpleExp expression =
  case expression
  of VarE {} -> True
     LitE {} -> True
     TyAppE {expOper = e} -> isSimpleExp e
     CallE {expOper = op} -> is_dictionary_operator op
     FunE {} -> False
     LetE {} -> False
     LetrecE {} -> False
     CaseE {} -> False
  where
    -- Dictionary constructor expressions are inlined to enable later
    -- optimizations
    is_dictionary_operator (VarE {expVar = c}) = isDictionaryCon c
    is_dictionary_operator (TyAppE {expOper = e}) = is_dictionary_operator e
    is_dictionary_operator (LetE {expBody = b}) = is_dictionary_operator b
    is_dictionary_operator _ = False

-- | Given a value and the pattern it is bound to, add the bound value(s)
-- to the environment.  The caller should verify that the value has no
-- side effects.  Any values that cannot be added to the environment will be
-- ignored.
bindValue :: RPat -> RExp -> PE a -> PE a
bindValue (WildP _)   _ m = m
bindValue (VarP v t)  e m | isSimpleExp e = local (Map.insert v e) m
                          | otherwise     = m
bindValue (TupleP ps) e m =
  case deconstructTupleExp e
  of Nothing -> m               -- Cannot bind this value
     Just es -> catEndo (zipWith bindValue ps es) m

-------------------------------------------------------------------------------

partialEvaluateModule :: RModule -> RModule
partialEvaluateModule (Module module_name defss exports) =
  let (defss', exports') = runPE (pevalDefGroups defss exports)
  in Module module_name defss' exports'

pevalDefGroups :: [DefGroup Rec] -> [Export Rec]
               -> PE ([DefGroup Rec], [Export Rec])
pevalDefGroups (defs:defss) exports = do
  (defs', (defss', exports')) <-
    pevalDefGroup defs $ pevalDefGroups defss exports
  return (defs' : defss', exports')

pevalDefGroups [] exports = do 
  exports' <- mapM pevalExport exports 
  return ([], exports')

pevalExport :: Export Rec -> PE (Export Rec)
pevalExport export = do
  fun <- pevalFun (exportFunction export)
  return $ export {exportFunction = fun}

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
pevalExp expression@(uncurryUnpackPolymorphicCall -> Just (op, ty_args, args)) = do
  -- Evaluate subexpressions
  args' <- mapM pevalExp args
  op' <- pevalExp op

  -- TODO: Try to statically evaluate this function
  return $ pevalApp (expInfo expression) op' (map SFType ty_args) args'

pevalExp expression =
  case expression
  of VarE {expInfo = inf, expVar = v}
       -- Replace constants with literal values.  This helps 
       -- representation selection represent these as values.
       | v `isPyonBuiltin` the_AdditiveDict_int_zero ->
           return $ LitE inf (IntL 0 (VarT $ pyonBuiltin the_int))
       | v `isPyonBuiltin` the_AdditiveDict_float_zero ->
           return $ LitE inf (FloatL 0 (VarT $ pyonBuiltin the_float))
       | v `isPyonBuiltin` the_MultiplicativeDict_int_one ->
           return $ LitE inf (IntL 1 (VarT $ pyonBuiltin the_int))
       | v `isPyonBuiltin` the_MultiplicativeDict_float_one ->
           return $ LitE inf (FloatL 1 (VarT $ pyonBuiltin the_float))
       | otherwise -> lookupVarDefault expression v
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

-- | Attempt to statically evalaute a known function.  The operands have
--   already been evaluated.
pevalApp inf op tys args =
  case known_oper
  of Just con
       | con `isPyonBuiltin` the_MultiplicativeDict_int_fromInt ->
           -- fromInt (n :: Int) = n
           case args of [arg] -> arg
       | con `isPyonBuiltin` the_MultiplicativeDict_float_fromInt ->
           -- fromInt (n :: Float) = n as a float
           case args
           of [LitE {expLit = IntL n _}] ->
                LitE { expInfo = inf
                     , expLit = FloatL (fromIntegral n) float_type}
              _ -> internalError "pevalApp"
     _ ->
       -- Can't evaluate; rebuild the call expression
       rebuild_call op tys args
  where
    -- Find the operator, if it is a constructor variable.
    -- Previous partial evaluation may have left useless 'let' expressions 
    -- around the operator.  Look through those.
    known_oper = find_known_oper op
      where
        find_known_oper (VarE {expVar = v}) = Just v
        find_known_oper (LetE {expBody = body}) = find_known_oper body
        find_known_oper (LetrecE {expBody = body}) = find_known_oper body
        find_known_oper _ = Nothing
                      
    rebuild_call op (t:ts) args =
      let op' = TyAppE inf op t
      in rebuild_call op' ts args

    rebuild_call op [] args = CallE inf op args
    
    float_type = VarT $ pyonBuiltin the_float

-- | Attempt to eliminate a case statement.  If the scrutinee is a constructor
-- application and it matches an alternative, replace the case statement
-- with the alternative.
eliminateCase :: SourcePos -> RExp -> [Alt Rec] -> Maybe RExp
eliminateCase pos scrutinee alternatives =
  -- Is the scrutinee a constructor application?
  case unpackPolymorphicCallAndBindings scrutinee
  of Just (bindings, VarE {expVar = scrutinee_con}, ty_args, args) ->
       -- Find a matching alternative
       case find ((scrutinee_con ==) . altConstructor) alternatives
       of Just alt ->
            -- Assume that type arguments match, because the code passed
            -- type checking.
            -- Bind parameters to the constructor's fields.
            Just $
            applyBindings bindings $
            foldr make_let (altBody alt) $
            zip args (altParams alt)
          Nothing -> Nothing    -- No matching alternative
     _ -> Nothing               -- Cannot determine constructor of scrutinee
  where
    make_let (arg, pat) expr =
      LetE { expInfo = mkSynInfo pos ObjectLevel
           , expBinder = pat
           , expValue = arg
           , expBody = expr
           }

pevalAlt :: Alt Rec -> PE (Alt Rec)
pevalAlt alt = do
  body' <- pevalExp $ altBody alt
  return $ alt {altBody = body'}
