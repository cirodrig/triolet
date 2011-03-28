{-| A specialized eta reduction transformation, to undo superfluous parameters 
inserted by the output-passing transformation.

When we see a function of the form @\x. f x@, where @x@ has representation
@OutPT@, remove the function parameter.  If that's the only parameter, then 
eliminate the function entirely.
-}

module SystemF.EtaReduce(etaReduceModule)
where

import Common.Error
import SystemF.Syntax
import SystemF.MemoryIR
import Type.Type

etaReduceModule :: Module Mem -> Module Mem
etaReduceModule (Module mod_name defss exports) =
  let defss' = map (fmap hrDef) defss
      exports' = map hrExport exports
  in Module mod_name defss' exports'

hrDef def = def {definiens = hrFun $ definiens def}

hrExport export =
  export {exportFunction = hrFun $ exportFunction export}

-- | Eta-reduce a function.  However, ensure that the function retains at
--   least one parameter or type parameter.
hrFun (FunM f) =
  case funParams f
  of ps@(_:_) | OutPT <- patMRepr (last ps),
          not (null $ init ps) || not (null $ funTyParams f) ->
       FunM (etaReduceFunction f)
     _ -> FunM (noEtaReduceFunction f)

-- Eta-reduce a function that is suitable for eta reduction
etaReduceFunction f =
  let out_param = last $ funParams f
      params = init $ funParams f
      mbody = etaReduceExp (patMVar out_param) $ funBody f
      ret_type = FunT (patMParamType out_param) (fromRetM (funReturn f))
  in case mbody
     of Just body -> f { funParams = params
                       , funBody = body
                       , funReturn = RetM (BoxRT ::: ret_type)}
        Nothing -> noEtaReduceFunction f

-- | Perform eta-reduction inside a function, but don't eta-reduce the function
noEtaReduceFunction f =
  f {funBody = case etaReduceExp Nothing $ funBody f
               of Just e -> e}

-- | Eta-reduce a lambda function, producing a new expression.  If the
--   function was eliminated, the new expression is the reduced function body.
hrLambdaFun :: ExpInfo -> FunM -> ExpM
hrLambdaFun inf (FunM f) =
  case funParams f
  of [] -> ExpM $ LamE inf (FunM $ noEtaReduceFunction f)
     ps | OutPT <- patMRepr (last ps) ->
       let f' = etaReduceFunction f
       in if null (funParams f') && null (funTyParams f')
          then funBody f'
          else ExpM $ LamE inf (FunM f')
     _ -> ExpM $ LamE inf (FunM $ noEtaReduceFunction f)

-- | When eta-reducing an expression, the argument to be stripped is passed
--   along as a parameter.
--
--   Because eta reduction causes side effects to be delayed, we
--   conservatively disallow eta reduction if there is a locally allocated
--   variable in the scope of the functions that are being modified.
--
--   TODO: Refactor into a non-failing recursive transformer and a failing
--   eta-reducer.
etaReduceExp :: Maybe Var -> ExpM -> Maybe ExpM
etaReduceExp strip_arg (ExpM expression) =
  case expression
  of VarE {} -> can't_strip
     LitE {} -> can't_strip
     AppE inf op ty_args args ->
       let op' = hrNonTail op
           args' = map hrNonTail args

           -- If stripping, the last argument must be a variable.
           -- The variable must match strip_arg.  Remove that argument.
           stripped_args =
             case strip_arg
             of Nothing -> args'
                Just v ->
                  case args'
                  of [] -> failed
                     _ -> case last args'
                          of ExpM (VarE _ arg_v) | v == arg_v -> init args'
                             _ -> failed
       in stripped_args `seq`
          return (ExpM (AppE inf op' ty_args stripped_args))
     LamE inf f -> return $ hrLambdaFun inf f
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
       let defs' = fmap hrDef defs
       body' <- hrTail body
       return $ ExpM (LetfunE inf defs' body')
     CaseE inf scr alts -> do
       let scr' = hrNonTail scr
       alts' <- mapM (etaReduceAlt strip_arg) alts
       return $ ExpM (CaseE inf scr' alts')
     ExceptE {} ->
       case strip_arg
       of Just _ ->
            -- Can't eta-reduce an exception, because it might cause
            -- the exception to be raised sooner
            Nothing
          Nothing -> return $ ExpM expression
  where
    hrNonTail e = case etaReduceExp Nothing e
                  of Just e' -> e'
    hrTail e = etaReduceExp strip_arg e

    failed = internalError "etaReduceExp"

    -- This expression can't be eta-reduced
    can't_strip = case strip_arg
                  of Nothing -> return $ ExpM expression
                     Just _ -> failed

etaReduceAlt strip_arg (AltM alt) = do
  body <- etaReduceExp strip_arg $ altBody alt
  return $ AltM $ alt {altBody = body}