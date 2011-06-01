{-| A specialized eta reduction transformation, to undo superfluous parameters 
inserted by the output-passing transformation.

When we see a function of the form @\x. f x@, where @x@ is an application of
@OutPT@, remove the function parameter.  If that's the only parameter, then 
eliminate the function entirely.
-}

module SystemF.EtaReduce(etaReduceModule,
                         etaReduceSingleFunction,
                         etaReduceSingleLambdaFunction)
where

import Data.Maybe

import Common.Error
import Builtins.Builtins
import SystemF.Syntax
import SystemF.MemoryIR
import Type.Type

-------------------------------------------------------------------------------
-- Entry points

etaReduceModule :: Module Mem -> Module Mem
etaReduceModule (Module mod_name defss exports) =
  let defss' = map (fmap (hrDef True)) defss
      exports' = map (hrExport True) exports
  in Module mod_name defss' exports'

-- | Eta-reduce a function.
--
--   Functions found inside the function body are not eta-reduced.
etaReduceSingleFunction :: FunM -> FunM
etaReduceSingleFunction f = hrFun False False f

-- | Eta-reduce a function and return an expression,
--   if it's suitable for eta reduction.
--   If all function parameters are eliminated by eta reduction, then the
--   eta-reduced function body is returned.  Otherwise a lambda expression
--   is returned.
--
--   Functions found inside the function body are not eta-reduced.
etaReduceSingleLambdaFunction :: Bool -> ExpInfo -> FunM -> ExpM
etaReduceSingleLambdaFunction allow_exceptions inf f =
  hrLambdaFun False allow_exceptions inf f

-------------------------------------------------------------------------------

-- | Return True if this parameter is used for passing an output variable
isOutputParameter :: PatM -> Bool
isOutputParameter pat =
  case fromVarApp (patMType pat)
  of Just (op, [arg]) | op `isPyonBuiltin` the_OutPtr -> True
     _ -> False

isNotOutputParameter = not . isOutputParameter

hrDef recurse def =
  def {definiens = hrFun recurse False $ definiens def}

hrExport recurse export =
  export {exportFunction = hrFun recurse False $ exportFunction export}

-- | Eta-reduce a function, if it's suitable for eta reduction.
--   Ensure that the function retains at least one parameter or
--   type parameter before we decide to eta-reduce it.
hrFun :: Bool -> Bool -> FunM -> FunM
hrFun recurse allow_exceptions (FunM f) =
  let out_param    = last $ funParams f
      other_params = init $ funParams f
  in if null (funParams f) ||                        -- No parameters
        null other_params && null (funTyParams f) || -- No non-output params
        isNotOutputParameter out_param -- Not output parameter
     then FunM (noEtaReduceFunction recurse allow_exceptions f)
     else case etaReduceFunction recurse allow_exceptions f out_param other_params
          of Just f -> FunM f
             Nothing -> FunM (noEtaReduceFunction recurse allow_exceptions f)

-- Eta-reduce a function that is suitable for eta reduction
etaReduceFunction recurse allow_exceptions f out_param params =
  let mbody = etaReduceExp recurse allow_exceptions (Just $ patMVar out_param) $ funBody f
      ret_type = patMType out_param `FunT` fromTypM (funReturn f)
  in case mbody
     of Just body ->
          Just $ f { funParams = params
                   , funBody = body
                   , funReturn = TypM ret_type}
        Nothing -> Nothing

-- | Don't eta-reduce a function.  If eta-reduction is being performed
--   recursively, then eta-reduce inside the function body.
noEtaReduceFunction True allow_exceptions f =
  f {funBody = case etaReduceExp True allow_exceptions Nothing $ funBody f
               of Just e -> e}

noEtaReduceFunction False _ f = f

-- | Eta-reduce a lambda function, producing a new expression.  If the
--   function was eliminated, the new expression is the reduced function body.
hrLambdaFun :: Bool -> Bool -> ExpInfo -> FunM -> ExpM
hrLambdaFun recurse allow_exceptions inf (FunM f)
  | null (funParams f) ||
    isNotOutputParameter out_param =
      -- Can't eta-reduce
      ExpM $ LamE inf (FunM $ noEtaReduceFunction recurse allow_exceptions f)
  | null other_params && null (funTyParams f) =
      -- The output parameter is the only parameter.
      -- Eta-reduce and eliminate the function, returning the function body.
      case etaReduceFunction recurse allow_exceptions f out_param other_params
      of Just f -> funBody f
         Nothing -> ExpM $ LamE inf (FunM $ noEtaReduceFunction recurse allow_exceptions f)
  | otherwise =
      -- Eta-reduce the function
      let new_f = 
            case etaReduceFunction recurse allow_exceptions f out_param other_params
            of Just f -> f
               Nothing -> noEtaReduceFunction recurse allow_exceptions f
      in ExpM $! LamE inf $! FunM $! new_f
  where 
    out_param    = last $ funParams f
    other_params = init $ funParams f

-- | When eta-reducing an expression, the argument to be stripped is passed
--   along as a parameter.
--
--   Because eta reduction causes side effects to be delayed, we
--   conservatively disallow eta reduction if there is a locally allocated
--   variable in the scope of the functions that are being modified.
--    
--   During the first eta reduction pass, @recurse@ is set to True so that 
--   all expressions are transformed.  During later passes, eta reduction is
--   performed on individual functions with @recurse@ set to false.  In this 
--   case, the goal is to eta-reduce only that function.  To accomplish that
--   goal, eta-reduction is only performed recursively in tail position.
--
--   TODO: Refactor into a non-failing recursive transformer and a failing
--   eta-reducer.
etaReduceExp :: Bool -> Bool -> Maybe Var -> ExpM -> Maybe ExpM
etaReduceExp recurse allow_exceptions strip_arg (ExpM expression) =
  case expression
  of VarE {} -> can't_strip
     LitE {} -> can't_strip
     AppE inf op ty_args args ->
       let op' = hrNonTail op
           args' = map hrNonTail args

       in do -- If stripping, the last argument must be a variable.
             -- The variable must match strip_arg.  Remove that argument.
             stripped_args <-
               case strip_arg
               of Nothing -> return args'
                  Just v
                    | null args' -> Nothing
                    | otherwise ->
                      case last args'
                      of ExpM (VarE _ arg_v)
                           | v == arg_v -> return $ init args'
                         _ -> Nothing
             return (ExpM (AppE inf op' ty_args stripped_args))
     LamE inf f -> return $ hrLambdaFun recurse allow_exceptions inf f
     LetE inf binder val body -> do
       let val' = hrNonTail val
       body' <- hrTail body
       return $ ExpM (LetE inf binder val' body')
     LetfunE inf defs body -> do
       let defs' = fmap (hrDef recurse) defs
       body' <- hrTail body
       return $ ExpM (LetfunE inf defs' body')
     CaseE inf scr alts -> do
       let scr' = hrNonTail scr
       alts' <- mapM (etaReduceAlt recurse allow_exceptions strip_arg) alts
       return $ ExpM (CaseE inf scr' alts')
     ExceptE {} ->
       -- This expression raises an exception.  In general, it's not safe to
       -- eta-reduce the enclosing function because that may cause the
       -- exception to be raised sooner.  If @strip_arg@ is false, the
       -- function isn't being eta-reduced so we don't care.
       -- If @allow_exceptions@ is true, then we know this code will be
       -- executed, so it's okay to raise the exception.
       if isJust strip_arg && not allow_exceptions
       then Nothing
       else return $ ExpM expression
  where
    hrNonTail e =
      -- During recursive eta-reduction, transform all subexpressions
      -- During nonrecursive eta-reduction, leave non-tail expressions alone
      -- Don't eta-reduce excepting statements in non-tail posiition
      if recurse
      then case etaReduceExp recurse False Nothing e of Just e' -> e'
      else e

    hrTail e = etaReduceExp recurse allow_exceptions strip_arg e

    failed = internalError "etaReduceExp"

    -- This expression can't be eta-reduced
    can't_strip = case strip_arg
                  of Nothing -> return $ ExpM expression
                     Just _ -> Nothing

etaReduceAlt recurse allow_exceptions strip_arg (AltM alt) = do
  body <- etaReduceExp recurse allow_exceptions strip_arg $ altBody alt
  return $ AltM $ alt {altBody = body}