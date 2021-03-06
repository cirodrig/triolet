-- | Partial evaluation.
-- This module collects several ways of simplifying Pyon code through a
-- sort of compile-time execution.  Copy propagation, constant propagation,
-- constant folding, un-currying, and case elimination are performed this way.
-- Partial evaluation maintains an \"execution environment\" of local variable
-- assignments.

{-# LANGUAGE ViewPatterns #-}
module SystemF.PartialEval()
where

  {-
import Prelude hiding(mapM)
import Control.Monad.Reader hiding(mapM)
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Traversable(mapM)

import Common.SourcePos
import Common.Error
import Builtins.Builtins
import SystemF.Syntax
import Type.Var
import Type.Type

catEndo :: [a -> a] -> a -> a
catEndo fs x = foldr ($) x fs

-- | The 'PE' monad holds the current variable-to-value assignment.
type PE a = Reader (Map.Map Var ExpSF) a

runPE m = runReader m Map.empty

-- | Look up the value of a variable
lookupVar :: Var -> PE (Maybe ExpSF)
lookupVar v = asks (Map.lookup v)

-- | Look up the value of a variable; supply a default value if none
-- is available
lookupVarDefault :: ExpSF -> Var -> PE ExpSF
lookupVarDefault defl v = asks (Map.findWithDefault defl v)

-- | Uncurry a function call.
--
-- Transform nested calls of the form @((f x y) z w)@ into flat calls
-- of the form @(f x y z w)@.
uncurryCall :: ExpSF -> ExpSF
uncurryCall (ExpSF op) = ExpSF $ fromMaybe op $ uncurryCall' op

-- | Uncurry a function call.  Return 'Nothing' if nothing changes.
uncurryCall' (AppE {expInfo = inf,
                    expOper = op,
                    expTyArgs = [],
                    expArgs = args}) =
  case uncurryCall op
  of ExpSF (AppE {expOper = op', expTyArgs = ty_args, expArgs = args'}) ->
       Just $ AppE {expInfo = inf, expOper = op', expTyArgs = ty_args,
                    expArgs = args' ++ args}
     _ -> Nothing

uncurryCall' _ = Nothing

-- | Uncurry and unpack a polymorphic function call.
uncurryUnpackPolymorphicCall e = unpackPolymorphicCall (uncurryCall e)

-- | Unpack a polymorphic call, possibly surrounded by let-expressions.
-- Return the unpacked call and bindings.
unpackPolymorphicCallAndBindings :: ExpSF
                                 -> Maybe ([(ExpInfo, PatSF, ExpSF)],
                                           ExpSF,
                                           [Type],
                                           [ExpSF])
unpackPolymorphicCallAndBindings expression =
  case fromExpSF expression
  of LetE { expInfo = inf
          , expBinder = pat
          , expValue = val
          , expBody = body} ->
       case unpackPolymorphicCallAndBindings body
       of Just (bindings, op, ty_args, args) ->
            Just ((inf, pat, val) : bindings, op, ty_args, args)
          Nothing -> Nothing
     _ -> case uncurryUnpackPolymorphicCall expression
          of Just (op, ty_args, args) -> Just ([], op, ty_args, args)
             Nothing -> Nothing

applyBindings :: [(ExpInfo, PatSF, ExpSF)] -> ExpSF -> ExpSF
applyBindings bs e = foldr make_let e bs
  where
    make_let (info, pat, rhs) body = ExpSF $ LetE info pat rhs body

-- | Return True if the expression is \"simple\" and thus worthy of
-- inlining.  We don't want to increase the amount of work performed by
-- by evaluating the same expression repeatedly, unless it is a known-cheap
-- expression.
isSimpleExp :: ExpSF -> Bool
isSimpleExp expression =
  case fromExpSF expression
  of VarE {} -> True
     LitE {} -> True
     ConE _ (VarCon v _ _) _ -> isDictionaryDataCon v
     ConE {} -> False
     AppE {} -> False
     LamE {} -> False
     LetE {} -> False
     LetfunE {} -> False
     CaseE {} -> False
     ExceptE {} -> False
     CoerceE {} -> False
     ArrayE {} -> False

-- | Given a value and the pattern it is bound to, add the bound value(s)
-- to the environment.  The caller should verify that the value has no
-- side effects.  Any values that cannot be added to the environment will be
-- ignored.
bindValue :: PatSF -> ExpSF -> PE a -> PE a
bindValue (VarP v _)  e m | isSimpleExp e = local (Map.insert v e) m
                          | otherwise     = m

-------------------------------------------------------------------------------

partialEvaluateModule :: Module SF -> Module SF
partialEvaluateModule (Module module_name [] defss exports) =
  let (defss', exports') = runPE (pevalDefGroups pevalGlobalDef defss exports)
  in Module module_name [] defss' exports'

pevalDefGroups :: (Def t SF -> PE (Def t SF))
               -> [DefGroup (Def t SF)] -> [Export SF]
               -> PE ([DefGroup (Def t SF)], [Export SF])
pevalDefGroups do_def (defs:defss) exports = do
  (defs', (defss', exports')) <-
    pevalDefGroup do_def defs $ pevalDefGroups do_def defss exports
  return (defs' : defss', exports')

pevalDefGroups _ [] exports = do
  exports' <- mapM pevalExport exports
  return ([], exports')

pevalExport :: Export SF -> PE (Export SF)
pevalExport export = do
  fun <- pevalFun (exportFunction export)
  return $ export {exportFunction = fun}

pevalDefGroup :: (Def t SF -> PE (Def t SF))
              -> DefGroup (Def t SF) -> PE a -> PE (DefGroup (Def t SF), a)
pevalDefGroup do_def dg m = do
  dg' <- mapM do_def dg
  x <- m
  return (dg', x)

pevalGlobalDef def = mapMDefiniens do_entity def
  where
    do_entity (FunEnt f) = FunEnt `liftM` pevalFun f
    do_entity (DataEnt d) = return $ DataEnt d

pevalDef :: FDef SF -> PE (FDef SF)
pevalDef def = mapMDefiniens pevalFun def

pevalFun :: FunSF -> PE FunSF
pevalFun (FunSF f) = do
  body <- pevalExp $ funBody f
  return $ FunSF $ f {funBody = body}

-- | Partial evaluation of an expression.
pevalExp :: ExpSF -> PE ExpSF
pevalExp expression =
  -- Since dictionary contents were changed to be boxed, this function's
  -- partial evaluation rules are no longer correct.
  error "This function is obsolete" $
  case fromExpSF (uncurryCall expression)
  of VarE {expInfo = inf, expVar = v}
       -- Replace constants with literal values.  This helps 
       -- representation selection represent these as values.
       | v `isCoreBuiltin` The_AdditiveDict_int_zero ->
           return_lit inf $ IntL 0 intT
       | v `isCoreBuiltin` The_AdditiveDict_float_zero ->
           return_lit inf $ FloatL 0 floatT
       | v `isCoreBuiltin` The_MultiplicativeDict_int_one ->
           return_lit inf $ IntL 1 intT
       | v `isCoreBuiltin` The_MultiplicativeDict_float_one ->
           return_lit inf $ FloatL 1 floatT
       | v `isCoreBuiltin` The_FloatingDict_float_pi ->
           return_lit inf $ FloatL pi floatT
       | otherwise -> lookupVarDefault expression v
     ConE inf op args -> do
       args' <- mapM pevalExp args
       return $ ExpSF $ ConE inf op args'
     LitE {} -> return expression
     AppE {expInfo = inf, expOper = op, expTyArgs = tys, expArgs = args} -> do
       op' <- pevalExp op
       args' <- mapM pevalExp args
       return $ pevalApp inf op' tys args'
     LamE {expInfo = inf, expFun = f} -> do
       f' <- pevalFun f
       return $ ExpSF $ LamE {expInfo = inf, expFun = f'}

     -- This expression is generated sometimes by SSA.
     -- Replace "let x = FOO in x" with FOO.  Continue simplifying FOO.
     LetE { expBinder = VarP v _
          , expValue = rhs
          , expBody = ExpSF (VarE {expVar = v'})}
       | v == v' ->
         pevalExp rhs
     LetE inf pat rhs body -> do
       rhs' <- pevalExp rhs     -- Simplify RHS
       body' <- bindValue pat rhs' $ pevalExp body -- Evaluate body
       return $ ExpSF $ LetE inf pat rhs' body'

     LetfunE inf defs body -> do
       (defs', body') <- pevalDefGroup pevalDef defs $ pevalExp body
       return $ ExpSF $ LetfunE inf defs' body'

     CaseE inf scr alts -> do
       scr' <- pevalExp scr

       -- If possible, eliminate this case statement
       case eliminateCase (getSourcePos inf) scr' alts of
         Just e -> pevalExp e
         Nothing -> do
           alts' <- mapM pevalAlt alts
           return $ ExpSF $ CaseE inf scr' alts'

     ExceptE inf ty ->
       return $ ExpSF $ ExceptE inf ty
     
     CoerceE inf from_t to_t body -> do
       body' <- pevalExp body
       return $ ExpSF $ CoerceE inf from_t to_t body'

     ArrayE inf ty es -> do
       es' <- mapM pevalExp es
       return $ ExpSF $ ArrayE inf ty es'
  where
    return_lit inf l = return $ ExpSF $ LitE inf l

-- | Attempt to statically evalaute a known function.  The operands have
--   already been evaluated.
pevalApp inf op tys args =
  case known_oper
  of Just con
       | con `isCoreBuiltin` The_FloatingDict_float_fromfloat ->
           -- fromFloat (n :: Float) = n
           case args of [arg] -> arg
       | con `isCoreBuiltin` The_MultiplicativeDict_int_fromInt ->
           -- fromInt (n :: Int) = n
           case args of [arg] -> arg
       | con `isCoreBuiltin` The_MultiplicativeDict_float_fromInt ->
           -- fromInt (n :: Float) = n as a float
           case args
           of [ExpSF (LitE {expLit = IntL n _})] ->
                ExpSF $ LitE { expInfo = inf
                             , expLit = FloatL (fromIntegral n) floatT}
              _ -> rebuild_call
     _ ->
       -- Can't evaluate; rebuild the call expression
       rebuild_call
  where
    -- Find the operator, if it is a constructor variable.
    -- Previous partial evaluation may have left useless 'let' expressions 
    -- around the operator.  Look through those.
    known_oper = find_known_oper (fromExpSF op)
      where
        find_known_oper (VarE {expVar = v}) =
          Just v
        find_known_oper (LetE {expBody = body}) =
          find_known_oper $ fromExpSF body
        find_known_oper (LetfunE {expBody = body}) =
          find_known_oper $ fromExpSF body
        find_known_oper _ = Nothing
                      
    rebuild_call = ExpSF $ AppE inf op tys args

-- | Attempt to eliminate a case statement.  If the scrutinee is a constructor
-- application and it matches an alternative, replace the case statement
-- with the alternative.
eliminateCase :: SourcePos -> ExpSF -> [AltSF] -> Maybe ExpSF
eliminateCase pos scrutinee alternatives =
  -- Is the scrutinee a constructor application?
  case unpackPolymorphicCallAndBindings scrutinee
  of Just (bindings, ExpSF (VarE {expVar = scrutinee_con}), ty_args, args) ->
       -- Find a matching alternative
       case find (match_alternative scrutinee_con) alternatives
       of Just (AltSF alt)
            | not $ null $ getAltExTypes alt ->
              internalError "eliminateCase: Not implemented for existential types"
            | otherwise ->
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
      ExpSF $ LetE (mkExpInfo pos) pat arg expr
    
    match_alternative scrutinee_con (AltSF alt) =
      case altCon alt
      of VarDeCon c _ _ -> c == scrutinee_con
         _ -> False

pevalAlt :: AltSF -> PE AltSF
pevalAlt (AltSF alt) = do
  body' <- pevalExp $ altBody alt
  return $ AltSF $ alt {altBody = body'}
-}