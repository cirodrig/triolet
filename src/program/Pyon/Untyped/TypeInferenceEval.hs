-- | The output of type inference is evaluated here.  Evaluation detects 
-- errors related to unification and produces regular System F output.

module Pyon.Untyped.TypeInferenceEval
       (evalTypeInferenceResult)
where

import Control.Concurrent.MVar
import Control.Monad

import Gluon.Common.Error
import Pyon.SystemF.Syntax
import qualified Pyon.Untyped.Data as Untyped

evType :: Untyped.TIType -> IO RType
evType (Untyped.DelayedType m) = m

evTyParam :: TyPat Untyped.TI -> IO RTyPat
evTyParam (TyPat v t) = TyPat v `liftM` evType t

evPat :: Pat Untyped.TI -> IO RPat
evPat (WildP t)   = WildP `liftM` evType t
evPat (VarP v t)  = VarP v `liftM` evType t
evPat (TupleP ps) = TupleP `liftM` mapM evPat ps

evExp :: Untyped.TIExp -> IO RExp
evExp expression =
  case expression
  of Untyped.RecVarPH {} -> getPlaceholderElaboration expression
     Untyped.DictPH {} -> getPlaceholderElaboration expression
     Untyped.TIExp e ->
       case e
       of VarE info v   -> return $ VarE info v
          ConE info c   -> return $ ConE info c
          LitE info l t -> do t' <- evType t
                              return $ LitE info l t'
          UndefinedE info t -> do t' <- evType t
                                  return $ UndefinedE info t'
          TyAppE info op t -> do op' <- evExp op
                                 t' <- evType t
                                 return $ TyAppE info op' t'
          CallE info op args -> do op' <- evExp op
                                   args' <- mapM evExp args
                                   return $ CallE info op' args'
          FunE info f -> do f' <- evFun f
                            return $ FunE info f'
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

evAlt (Alt c ty_params params body) = do
  ty_params' <- mapM evType ty_params
  body' <- evExp body
  return $ Alt c ty_params' params body'

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
  return $ Fun { funTyParams = ty_params
               , funParams = params
               , funReturnType = rt
               , funBody = body
               }

evDef :: Def Untyped.TI -> IO RDef
evDef (Def v f) = Def v `liftM` evFun f

evalTypeInferenceResult :: Module Untyped.TI -> IO RModule
evalTypeInferenceResult (Module defs exports) = do
  defs' <- mapM (mapM evDef) defs
  return $ Module defs' exports
