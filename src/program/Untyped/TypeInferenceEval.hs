-- | The output of type inference is evaluated here.  Evaluation detects 
-- errors related to unification and produces regular System F output.

module Untyped.TypeInferenceEval
       (evalTypeInferenceResult)
where

import Prelude hiding(mapM)
import Control.Concurrent.MVar
import Control.Monad hiding(mapM)
import Data.Traversable(mapM)

import Common.Error
import SystemF.Syntax
import Type.Type
import qualified Untyped.Data as Untyped

evTypSF :: Untyped.TIType -> IO TypSF
evTypSF (Untyped.DelayedType m) = m

evType :: Untyped.TIType -> IO Type
evType (Untyped.DelayedType m) = fmap fromTypSF m

evTyParam :: TyPat Untyped.TI -> IO (TyPat SF)
evTyParam (Untyped.TITyPat v t) = do
  t' <- evType t
  return (TyPatSF (v ::: t'))

evPat :: Pat Untyped.TI -> IO PatSF
evPat (Untyped.TIWildP t)   = WildP `liftM` evType t
evPat (Untyped.TIVarP v t)  = VarP v `liftM` evType t
evPat (Untyped.TITupleP ps) = TupleP `liftM` mapM evPat ps


evExp :: Untyped.TIExp -> IO ExpSF
evExp expression =
  case expression
  of Untyped.RecVarPH {} -> getPlaceholderElaboration expression
     Untyped.DictPH {} -> getPlaceholderElaboration expression
     Untyped.TIExp e -> fmap ExpSF $
       case e
       of VarE info v   -> return $ VarE info v
          LitE info l   -> return $ LitE info l
          AppE info op ts args -> do op' <- evExp op
                                     ts' <- mapM evTypSF ts
                                     args' <- mapM evExp args
                                     return $ AppE info op' ts' args'
          LamE info f -> do f' <- evFun f
                            return $ LamE info f'
          LetE info p r b -> do p' <- evPat p
                                r' <- evExp r
                                b' <- evExp b
                                return $ LetE info p' r' b'
          LetfunE info defs b -> do defs' <- mapM evDef defs
                                    b' <- evExp b
                                    return $ LetfunE info defs' b'
          CaseE info scr alts -> do scr' <- evExp scr
                                    alts' <- mapM evAlt alts
                                    return $ CaseE info scr' alts'
          CoerceE info from_t to_t b -> do from_t' <- evTypSF from_t
                                           to_t' <- evTypSF to_t
                                           b' <- evExp b
                                           return $ CoerceE info from_t' to_t' b'
     Untyped.TIRecExp e -> return e

evAlt (Untyped.TIAlt (DeCon c ty_params ex_types params body)) = do
  ty_params' <- mapM evTypSF ty_params
  ex_types' <- mapM evTyParam ex_types
  body' <- evExp body
  params' <- mapM evPat params
  return $ AltSF $ DeCon c ty_params' ex_types' params' body'

-- | Get the expression that was stored for a placeholder, and evaluate it
getPlaceholderElaboration ph = do
  is_empty <- isEmptyMVar $ Untyped.phExpResolution ph
  when is_empty $ internalError "Unresolved placeholder"
  evExp =<< readMVar (Untyped.phExpResolution ph)

evFun :: Fun Untyped.TI -> IO FunSF
evFun (Untyped.TIFun f) = do
  ty_params <- mapM evTyParam $ funTyParams f
  params <- mapM evPat $ funParams f
  rt <- evType $ funReturn f
  body <- evExp $ funBody f
  return $ FunSF $ Fun { funInfo = funInfo f
                       , funTyParams = ty_params
                       , funParams = params
                       , funReturn = TypSF rt
                       , funBody = body
                       }

evDef :: Def Untyped.TI -> IO (Def SF)
evDef def = mapMDefiniens evFun def

evExport :: Export Untyped.TI -> IO (Export SF)
evExport (Export pos spec f) = Export pos spec `liftM` evFun f

evalTypeInferenceResult :: Module Untyped.TI -> IO (Module SF)
evalTypeInferenceResult (Module module_name [] defs exports) = do
  defs' <- mapM (mapM evDef) defs
  exports' <- mapM evExport exports
  return $ Module module_name [] defs' exports'
