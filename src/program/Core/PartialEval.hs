{-| Partial evaluation of Core expressions.
-}



module Core.PartialEval
       (partialEvaluate)
where

import Gluon.Common.Error
import Gluon.Core(Rec)
import qualified Gluon.Core as Gluon
import qualified SystemF.Builtins as SF
import Core.Syntax

dummyAddress :: AddrExp Rec
dummyAddress = Gluon.mkInternalVarE (SF.pyonBuiltin SF.the_dummy_addr)

-- | Eliminate a function application, putting an instance of the function
-- body in place of the function.  Parameters are converted to
-- @let@ expressions.
--
-- > (\a b c. bar (foo a b) c) x y (z_big_expression 1 True 3 4)
--
-- Becomes
--
-- > let a = x
-- > let b = y
-- > let c = z_big_expression 1 True 3 4
-- > in bar (foo x y) c
eliminateFun :: RCFun           -- ^ Function to eliminate
             -> [RCExp]         -- ^ Argument expressions; @True@ to substitute
             -> Maybe RCExp     -- ^ Return expression
             -> RCExp
eliminateFun f args mrarg =
  assign_parameters (cfunParams f) args $
  replace_return_arg mrarg $
  cfunBody f
  where
    assign_parameters params args e =
      foldr assign_parameter e (zip params args)
    
    assign_parameter (ValP v ::: t, arg) e =
      LetCE (cfunInfo f) (ValB v ::: t) arg e

    assign_parameter (OwnP v ::: t, arg) e =
      LetCE (cfunInfo f) (OwnB v ::: t) arg e
    
    assign_parameter (ReadP a v ::: t, arg) e =
      -- FIXME: need type inference to get the actual address!
      LetCE (cfunInfo f) (RefB dummyAddress v ::: t) arg e

    replace_return_arg Nothing e =
      case fromCBind (cfunReturn f)
      of ValR -> e
         OwnR -> e
         _ -> internalError "replace_return_arg: Missing return argument"

    replace_return_arg (Just rarg) e =
      case fromCBind (cfunReturn f)
      of WriteR a p -> substituteReturnArgument p rarg e
         _ -> internalError "replace_return_arg: Unexpected return argument"

substituteReturnArgument :: PtrVar -> RCExp -> RCExp -> RCExp
substituteReturnArgument return_ptr argument expression = s_exp expression
  where
    s_exp expr =
      case expr
      of ValCE {cexpVal = WriteVarV _ p} | return_ptr == p -> argument
         ValCE {} -> expr
         AppCE {cexpOper = op, cexpArgs = args, cexpReturnArg = ra} ->
           let ra' = fmap s_exp ra
               op' = s_exp op
               args' = map s_exp args
           in expr {cexpOper = op',cexpArgs = args', cexpReturnArg = ra'}
         LamCE {cexpFun = f} ->
           expr {cexpFun = s_fun f}
         LetCE {cexpRhs = rhs, cexpBody = body} ->
           let rhs' = s_exp rhs
               body' = s_exp body
           in expr {cexpRhs = rhs', cexpBody = body'}
         LetrecCE {cexpDefs = defs, cexpBody = body} ->
           let defs' = map s_def defs
               body' = s_exp body
           in expr {cexpDefs = defs', cexpBody = body'}
         CaseCE {cexpScrutinee = scr, cexpAlternatives = alts} ->
           let scr' = s_exp scr
               alts' = map s_alt alts
           in expr {cexpScrutinee = scr', cexpAlternatives = alts'}

    s_fun f =
      let body' = s_exp (cfunBody f)
      in f {cfunBody = body'}
    
    s_def (CDef v f) = CDef v (s_fun f)
    
    s_alt alt =
      let body' = s_exp (caltBody alt)
      in alt {caltBody = body'}

-- | Elimination
pevalExp :: RCExp -> RCExp
pevalExp expression =
  case expression
  of ValCE {} -> expression
     AppCE { cexpOper = LamCE {cexpFun = fun}
           , cexpArgs = args
           , cexpReturnArg = mra}
       | length args == length (cfunParams fun) ->
         -- Apply the function to its arguments
         eliminateFun fun args mra
     AppCE {cexpOper = op, cexpArgs = args, cexpReturnArg = mra} ->
       let op' = pevalExp op
           args' = map pevalExp args
           mra' = fmap pevalExp mra
       in expression {cexpOper = op', cexpArgs = args', cexpReturnArg = mra'} 
     LamCE {cexpFun = fun} ->
       expression {cexpFun = pevalFun fun}
     LetCE {cexpBinder = b, cexpRhs = rhs, cexpBody = body} ->
       let rhs' = pevalExp rhs
           body' = pevalExp body
       in expression {cexpRhs = rhs', cexpBody = body}
     LetrecCE {cexpDefs = defs, cexpBody = body} ->
       let defs' = map pevalDef defs
           body' = pevalExp body
       in expression {cexpDefs = defs', cexpBody = body'}
     CaseCE {cexpScrutinee = scr, cexpAlternatives = alts} ->
       let scr' = pevalExp scr
           alts' = map pevalAlt alts
       in expression {cexpScrutinee = scr', cexpAlternatives = alts'}
          
pevalFun :: RCFun -> RCFun
pevalFun f = f {cfunBody = pevalExp (cfunBody f)}

pevalDef (CDef v f) = CDef v (pevalFun f)

pevalAlt alt = alt {caltBody = pevalExp (caltBody alt)}

partialEvaluate :: CModule Rec -> CModule Rec
partialEvaluate mod =
  mod {cmodDefs = map (map pevalDef) $ cmodDefs mod}