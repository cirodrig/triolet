-- | Partial evaluation.
-- This module collects several ways of simplifying Pyon code through a
-- sort of compile-time execution.  Copy propagation, constant propagation,
-- constant folding, un-currying, and case elimination are performed this way.
-- Partial evaluation maintains an \"execution environment\" of local variable
-- assignments.

{-# LANGUAGE ViewPatterns #-}
module SystemF.PartialEval(partialEvaluateModule)
where

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

-- | If the expression is a tuple expression, then return the expression's
-- field values.
deconstructTupleExp :: ExpSF -> Maybe [ExpSF]
deconstructTupleExp expression =
  -- If the operator is a tuple value constructor, then return the arguments
  -- otherwise, return nothing
  case uncurryUnpackPolymorphicCall expression
  of Just (ExpSF (VarE {expVar = con}), ty_args, args)
       | isPyonTupleCon con -> Just args
     _ -> Nothing

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
                                           [TypSF],
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
          of Just (op, ty_args, args) -> Just ([], op, map TypSF ty_args, args)
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
     AppE {expOper = op} -> is_dictionary_operator (fromExpSF op)
     LamE {} -> False
     LetE {} -> False
     LetfunE {} -> False
     CaseE {} -> False
  where
    -- Dictionary constructor expressions are inlined to enable later
    -- optimizations
    is_dictionary_operator (VarE {expVar = c}) = isDictionaryTypeCon c
    is_dictionary_operator (LetE {expBody = b}) =
      is_dictionary_operator $ fromExpSF b
    is_dictionary_operator _ = False

-- | Given a value and the pattern it is bound to, add the bound value(s)
-- to the environment.  The caller should verify that the value has no
-- side effects.  Any values that cannot be added to the environment will be
-- ignored.
bindValue :: PatSF -> ExpSF -> PE a -> PE a
bindValue (WildP _)   _ m = m
bindValue (VarP v _)  e m | isSimpleExp e = local (Map.insert v e) m
                          | otherwise     = m
bindValue (TupleP ps) e m =
  case deconstructTupleExp e
  of Nothing -> m               -- Cannot bind this value
     Just es -> catEndo (zipWith bindValue ps es) m

-------------------------------------------------------------------------------

partialEvaluateModule :: Module SF -> Module SF
partialEvaluateModule (Module module_name defss exports) =
  let (defss', exports') = runPE (pevalDefGroups defss exports)
  in Module module_name defss' exports'

pevalDefGroups :: [DefGroup (Def SF)] -> [Export SF]
               -> PE ([DefGroup (Def SF)], [Export SF])
pevalDefGroups (defs:defss) exports = do
  (defs', (defss', exports')) <-
    pevalDefGroup defs $ pevalDefGroups defss exports
  return (defs' : defss', exports')

pevalDefGroups [] exports = do
  exports' <- mapM pevalExport exports
  return ([], exports')

pevalExport :: Export SF -> PE (Export SF)
pevalExport export = do
  fun <- pevalFun (exportFunction export)
  return $ export {exportFunction = fun}

pevalDefGroup :: DefGroup (Def SF) -> PE a -> PE (DefGroup (Def SF), a)
pevalDefGroup dg m = do
  dg' <- mapM pevalDef dg
  x <- m
  return (dg', x)

pevalDef :: Def SF -> PE (Def SF)
pevalDef (Def v f) = do
  f' <- pevalFun f
  return $ Def v f'

pevalFun :: FunSF -> PE FunSF
pevalFun (FunSF f) = do
  body <- pevalExp $ funBody f
  return $ FunSF $ f {funBody = body}

-- | Partial evaluation of an expression.
pevalExp :: ExpSF -> PE ExpSF
pevalExp expression =
  case fromExpSF (uncurryCall expression)
  of VarE {expInfo = inf, expVar = v}
       -- Replace constants with literal values.  This helps 
       -- representation selection represent these as values.
       | v `isPyonBuiltin` the_AdditiveDict_int_zero ->
           return_lit inf $ IntL 0 int_type
       | v `isPyonBuiltin` the_AdditiveDict_float_zero ->
           return_lit inf $ FloatL 0 float_type
       | v `isPyonBuiltin` the_MultiplicativeDict_int_one ->
           return_lit inf $ IntL 1 int_type
       | v `isPyonBuiltin` the_MultiplicativeDict_float_one ->
           return_lit inf $ FloatL 1 float_type
       | v `isPyonBuiltin` the_FloatingDict_float_pi ->
           return_lit inf $ FloatL pi float_type
       | otherwise -> lookupVarDefault expression v
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
       (defs', body') <- pevalDefGroup defs $ pevalExp body
       return $ ExpSF $ LetfunE inf defs' body'

     CaseE inf scr alts -> do
       scr' <- pevalExp scr

       -- If possible, eliminate this case statement
       case eliminateCase (getSourcePos inf) scr' alts of
         Just e -> pevalExp e
         Nothing -> do
           alts' <- mapM pevalAlt alts
           return $ ExpSF $ CaseE inf scr' alts'
  where
    return_lit inf l = return $ ExpSF $ LitE inf l
    int_type = VarT $ pyonBuiltin the_int
    float_type = VarT $ pyonBuiltin the_float

-- | Attempt to statically evalaute a known function.  The operands have
--   already been evaluated.
pevalApp inf op tys args =
  case known_oper
  of Just con
       | con `isPyonBuiltin` the_FloatingDict_float_fromfloat ->
           -- fromFloat (n :: Float) = n
           case args of [arg] -> arg
       | con `isPyonBuiltin` the_MultiplicativeDict_int_fromInt ->
           -- fromInt (n :: Int) = n
           case args of [arg] -> arg
       | con `isPyonBuiltin` the_MultiplicativeDict_float_fromInt ->
           -- fromInt (n :: Float) = n as a float
           case args
           of [ExpSF (LitE {expLit = IntL n _})] ->
                ExpSF $ LitE { expInfo = inf
                             , expLit = FloatL (fromIntegral n) float_type}
              _ -> internalError "pevalApp"
       | con `isPyonBuiltin` the_TraversableDict_list_traverse ->
           case rewriteTraverseExpresion inf tys args
           of Just new_exp -> new_exp
              Nothing -> rebuild_call op tys args
     _ ->
       -- Can't evaluate; rebuild the call expression
       rebuild_call op tys args
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
                      
    rebuild_call op ts args = ExpSF $ AppE inf op ts args
    
    float_type = VarT $ pyonBuiltin the_float

-- The defaulting rules sometimes make a polymorphic function return a list
-- which is then converted to a stream.  For some known functions, we change 
-- the code to return a Stream and eliminate the conversion.
rewriteTraverseExpresion inf [return_type] [return_repr, input] =
  case unpackPolymorphicCallAndBindings input
  of Just (bindings, ExpSF (VarE {expVar = input_op}), ty_args, args)
       | input_op `isPyonBuiltin` the_fun_zip ->
         case ty_args
         of [container1, container2, _, elem1, elem2] ->
              case args
              of [trav1, trav2, _, repr1, repr2, input1, input2] ->
                   -- Replace the output container and traversable types
                   let oper =
                         ExpSF $ VarE inf (pyonBuiltin the_fun_zip)
                   in Just $ applyBindings bindings $ ExpSF $ AppE inf oper
                      [container1, container2,
                       TypSF $ VarT (pyonBuiltin the_Stream), elem1, elem2]
                      [trav1, trav2, traversable_Stream, repr1, repr2,
                       input1, input2]
       | input_op `isPyonBuiltin` the_fun_map ->
         case ty_args
         of [container1, _, in_type, out_type] ->
              case args
              of [trav1, _, in_repr, out_repr, fun, input] ->
                   -- Replace the output container and traversable types
                   let oper =
                         ExpSF $ VarE inf (pyonBuiltin the_fun_map)
                   in Just $ applyBindings bindings $ ExpSF $ AppE inf oper
                      [container1, TypSF $ VarT (pyonBuiltin the_Stream),
                       in_type, out_type]
                      [trav1, traversable_Stream, in_repr, out_repr, input]
     _ -> Nothing
  where
    -- The traversable dictionary for the Stream type
    traversable_Stream =
      ExpSF $ AppE defaultExpInfo
      (ExpSF $ VarE defaultExpInfo (pyonBuiltin the_traversableDict))
      [TypSF $ VarT (pyonBuiltin the_Stream)]
      [ExpSF $ VarE defaultExpInfo (pyonBuiltin the_TraversableDict_Stream_traverse),
       ExpSF $ VarE defaultExpInfo (pyonBuiltin the_TraversableDict_Stream_build)]

rewriteTraverseExpresion _ _ _ = Nothing
  
-- | Attempt to eliminate a case statement.  If the scrutinee is a constructor
-- application and it matches an alternative, replace the case statement
-- with the alternative.
eliminateCase :: SourcePos -> ExpSF -> [AltSF] -> Maybe ExpSF
eliminateCase pos scrutinee alternatives =
  -- Is the scrutinee a constructor application?
  case unpackPolymorphicCallAndBindings scrutinee
  of Just (bindings, ExpSF (VarE {expVar = scrutinee_con}), ty_args, args) ->
       -- Find a matching alternative
       case find ((scrutinee_con ==) . altConstructor) $ map fromAltSF alternatives
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
      ExpSF $ LetE (mkExpInfo pos) pat arg expr

pevalAlt :: AltSF -> PE AltSF
pevalAlt (AltSF alt) = do
  body' <- pevalExp $ altBody alt
  return $ AltSF $ alt {altBody = body'}
