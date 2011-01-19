-- | The output of type inference is evaluated here.  Evaluation detects 
-- errors related to unification and produces regular System F output.

module Untyped.TypeInferenceEval
       (evalTypeInferenceResult)
where

import Control.Concurrent.MVar
import Control.Monad

import Gluon.Common.Error
import qualified Gluon.Core.Syntax as Gluon
import SystemF.Syntax
import Type.Type
import Type.Var
import qualified Untyped.Data as Untyped

evType :: Untyped.TIType -> IO RType
evType (Untyped.DelayedType m) = m

evTyParam :: TyPat Untyped.TI -> IO RTyPat
evTyParam (TyPat v t) = TyPat v `liftM` evType t

evPat :: Pat Untyped.TI -> IO RPat
evPat (Untyped.TIWildP t)   = WildP `liftM` evType t
evPat (Untyped.TIVarP v t)  = VarP v `liftM` evType t
evPat (Untyped.TITupleP ps) = TupleP `liftM` mapM evPat ps


evExp :: Untyped.TIExp -> IO RExp
evExp expression =
  case expression
  of Untyped.RecVarPH {} -> getPlaceholderElaboration expression
     Untyped.DictPH {} -> getPlaceholderElaboration expression
     Untyped.TIExp e ->
       case e
       of VarE info v   -> return $ VarE info v
          LitE info l   -> return $ LitE info l
          AppE info op ts args -> do op' <- evExp op
                                     ts' <- mapM evType ts
                                     args' <- mapM evExp args
                                     return $ AppE info op' ts' args'
          LamE info f -> do f' <- evFun f
                            return $ LamE info f'
          LetE info p r b -> do p' <- evPat p
                                r' <- evExp r
                                b' <- evExp b
                                return $ LetE info p' r' b'
          LetrecE info defs b -> do defs' <- mapM evDef defs
                                    b' <- evExp b
                                    return $ LetrecE info defs' b'
          CaseE info scr alts -> do scr' <- evExp scr
                                    alts' <- mapM evAlt alts
                                    return $ CaseE info scr' alts'
          {- MethodSelectE inf cls t i e -> do t' <- evType t
                                            e' <- evExp e
                                            return $ MethodSelectE inf cls t' i e' -}
     Untyped.TIRecExp e -> return e

evAlt (Untyped.TIAlt (Alt c ty_params params body)) = do
  ty_params' <- mapM evType ty_params
  body' <- evExp body
  params' <- mapM evPat params
  return $ Alt c ty_params' params' body'

-- | Get the expression that was stored for a placeholder, and evaluate it
getPlaceholderElaboration ph = do
  is_empty <- isEmptyMVar $ Untyped.phExpResolution ph
  when is_empty $ internalError "Unresolved placeholder"
  evExp =<< readMVar (Untyped.phExpResolution ph)

evFun :: Fun Untyped.TI -> IO RFun
evFun (Untyped.TIFun f) = do
  ty_params <- mapM evTyParam $ funTyParams f
  params <- mapM evPat $ funParams f
  rt <- evType $ funReturnType f
  body <- evExp $ funBody f
  return $ Fun { funInfo = funInfo f
               , funTyParams = ty_params
               , funParams = params
               , funReturnType = rt
               , funBody = body
               }

evDef :: Def Untyped.TI -> IO RDef
evDef (Def v f) = Def v `liftM` evFun f

evExport :: Export Untyped.TI -> IO (Export Rec)
evExport (Export pos spec f) = Export pos spec `liftM` evFun f

evalTypeInferenceResult :: Module Untyped.TI -> IO RModule
evalTypeInferenceResult (Module module_name defs exports) = do
  defs' <- mapM (mapM evDef) defs
  exports' <- mapM evExport exports
  return $ Module module_name defs' exports'
