{-| A specialized eta reduction transformation, to undo superfluous parameters 
inserted by the output-passing transformation.

When we see a function of the form @\x. f x@, where @x@ has representation
@OutPT@, remove the function parameter.  If that's the only parameter, then 
eliminate the function entirely.
-}

module SystemF.EtaReduce(etaReduceModule,
                         etaReduceSingleFunction,
                         etaReduceSingleLambdaFunction)
where

import Common.Error
import SystemF.Syntax
import SystemF.MemoryIR
import Type.Type

etaReduceModule :: Module Mem -> Module Mem
etaReduceModule (Module mod_name defss exports) =
  let defss' = map (fmap (hrDef True)) defss
      exports' = map (hrExport True) exports
  in Module mod_name defss' exports'

-- | Eta-reduce a function, if it's suitable for eta reduction.
--
--   Functions found inside the function body are not eta-reduced.
etaReduceSingleFunction :: FunM -> FunM
etaReduceSingleFunction f = hrFun False f

-- | Eta-reduce a function and return an expression,
--   if it's suitable for eta reduction.
--   If all function parameters are eliminated by eta reduction, then the
--   eta-reduced function body is returned.  Otherwise a lambda expression
--   is returned.
--
--   Functions found inside the function body are not eta-reduced.
etaReduceSingleLambdaFunction :: ExpInfo -> FunM -> ExpM
etaReduceSingleLambdaFunction inf f = hrLambdaFun False inf f

hrDef recurse def = def {definiens = hrFun recurse $ definiens def}

hrExport recurse export =
  export {exportFunction = hrFun recurse $ exportFunction export}

-- | Eta-reduce a function, if it's suitable for eta reduction.
--   Ensure that the function retains at least one parameter or
--   type parameter before we decide to eta-reduce it.
hrFun :: Bool -> FunM -> FunM
hrFun recurse (FunM f) =
  let out_param    = last $ funParams f
      other_params = init $ funParams f
  in if null (funParams f) ||                        -- No parameters
        null other_params && null (funTyParams f) || -- No non-output params
        not (OutPT `sameParamRepr` patMRepr out_param) -- Not output parameter
     then FunM (noEtaReduceFunction recurse f)
     else case etaReduceFunction recurse f out_param other_params
          of Just f -> FunM f
             Nothing -> FunM (noEtaReduceFunction recurse f)

-- Eta-reduce a function that is suitable for eta reduction
etaReduceFunction recurse f out_param params =
  let mbody = etaReduceExp recurse (patMVar out_param) $ funBody f
      ret_type = FunT (patMParamType out_param) (fromRetM (funReturn f))
  in case mbody
     of Just body ->
          Just $ f { funParams = params
                   , funBody = body
                   , funReturn = RetM (BoxRT ::: ret_type)}
        Nothing -> Nothing

-- | Don't eta-reduce a function.  If eta-reduction is being performed
--   recursively, then eta-reduce inside the function body.
noEtaReduceFunction True f =
  f {funBody = case etaReduceExp True Nothing $ funBody f
               of Just e -> e}

noEtaReduceFunction False f = f

-- | Eta-reduce a lambda function, producing a new expression.  If the
--   function was eliminated, the new expression is the reduced function body.
hrLambdaFun :: Bool -> ExpInfo -> FunM -> ExpM
hrLambdaFun recurse inf (FunM f)
  | null (funParams f) ||
    not (OutPT `sameParamRepr` patMRepr out_param) =
      -- Can't eta-reduce
      ExpM $ LamE inf (FunM $ noEtaReduceFunction recurse f)
  | null other_params && null (funTyParams f) =
      -- The output parameter is the only parameter.
      -- Eta-reduce and eliminate the function, returning the function body.
      case etaReduceFunction recurse f out_param other_params
      of Just f -> funBody f
         Nothing -> ExpM $ LamE inf (FunM $ noEtaReduceFunction recurse f)
  | otherwise =
      -- Eta-reduce the function
      let new_f = 
            case etaReduceFunction recurse f out_param other_params
            of Just f -> f
               Nothing -> noEtaReduceFunction recurse f
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
etaReduceExp :: Bool -> Maybe Var -> ExpM -> Maybe ExpM
etaReduceExp recurse strip_arg (ExpM expression) =
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
     LamE inf f -> return $ hrLambdaFun recurse inf f
     LetE inf (LocalVarP pat_var pat_type pat_dict pat_dmd) val body ->
       case strip_arg
       of Just _ -> Nothing -- Can't eta-reduce
          Nothing -> do
            let val' = hrNonTail val
                dict' = hrNonTail pat_dict
                pat' = LocalVarP pat_var pat_type dict' pat_dmd
            body' <- hrTail body
            return $ ExpM (LetE inf pat' val' body')
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
       alts' <- mapM (etaReduceAlt recurse strip_arg) alts
       return $ ExpM (CaseE inf scr' alts')
     ExceptE {} ->
       case strip_arg
       of Just _ ->
            -- Can't eta-reduce an exception, because it might cause
            -- the exception to be raised sooner
            Nothing
          Nothing -> return $ ExpM expression
  where
    hrNonTail e =
      -- During recursive eta-reduction, transform all subexpressions
      -- During nonrecursive eta-reduction, leave non-tail expressions alone
      if recurse
      then case etaReduceExp recurse Nothing e of Just e' -> e'
      else e

    hrTail e = etaReduceExp recurse strip_arg e

    failed = internalError "etaReduceExp"

    -- This expression can't be eta-reduced
    can't_strip = case strip_arg
                  of Nothing -> return $ ExpM expression
                     Just _ -> Nothing

etaReduceAlt recurse strip_arg (AltM alt) = do
  body <- etaReduceExp recurse strip_arg $ altBody alt
  return $ AltM $ alt {altBody = body}