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

hrDef (Def v f) = Def v (hrFun f)

hrExport export =
  export {exportFunction = hrFun $ exportFunction export}

-- | Eta-reduce a function.  However, ensure that the function retains at
--   least one parameter or type parameter.
hrFun (FunM f) =
  case funParams f
  of ps@(_:_) | MemVarP _ (OutPT ::: _) <- last ps,
          not (null $ init ps) || not (null $ funTyParams f) ->
       FunM (etaReduceFunction f)
     _ -> FunM (noEtaReduceFunction f)

-- Eta-reduce a function that is suitable for eta reduction
etaReduceFunction f =
  let MemVarP param_var param_repr = last $ funParams f
      params = init $ funParams f
      body = etaReduceExp (Just param_var) $ funBody f
      ret_type = FunT param_repr (fromRetM (funReturn f))
  in f { funParams = params
       , funBody = body
       , funReturn = RetM (BoxRT ::: ret_type)}

-- | Perform eta-reduction inside a function, but don't eta-reduce the function
noEtaReduceFunction f =
  f {funBody = etaReduceExp Nothing $ funBody f}

-- | Eta-reduce a lambda function, producing a new expression.  If the
--   function was eliminated, the new expression is the reduced function body.
hrLambdaFun :: ExpInfo -> FunM -> ExpM
hrLambdaFun inf (FunM f) =
  case funParams f
  of [] -> ExpM $ LamE inf (FunM $ noEtaReduceFunction f)
     ps | MemVarP _ (OutPT ::: _) <- last ps ->
       let f' = etaReduceFunction f
       in if null (funParams f') && null (funTyParams f')
          then funBody f'
          else ExpM $ LamE inf (FunM f')
     _ -> ExpM $ LamE inf (FunM $ noEtaReduceFunction f)

-- | When eta-reducing an expression, the argument to be stripped is passed
--   along as a parameter.
etaReduceExp :: Maybe Var -> ExpM -> ExpM
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
       in stripped_args `seq` ExpM (AppE inf op' ty_args stripped_args)
     LamE inf f -> hrLambdaFun inf f
     LetE inf binder val body ->
       let val' = hrNonTail val
           body' = hrTail body
       in ExpM (LetE inf binder val' body')
     LetfunE inf defs body ->
       let defs' = fmap hrDef defs
           body' = hrTail body
       in ExpM (LetfunE inf defs' body')
     CaseE inf scr alts ->
       let scr' = hrNonTail scr
           alts' = map (etaReduceAlt strip_arg) alts
       in ExpM (CaseE inf scr' alts')
  where
    hrNonTail e = etaReduceExp Nothing e
    hrTail e = etaReduceExp strip_arg e

    failed = internalError "etaReduceExp"

    -- This expression can't be eta-reduced
    can't_strip = case strip_arg
                  of Nothing -> ExpM expression
                     Just _ -> failed

etaReduceAlt strip_arg (AltM alt) =
  AltM $ alt {altBody = etaReduceExp strip_arg $ altBody alt}