-- | The output of type inference is evaluated here.  Evaluation detects 
-- errors related to unification and produces regular System F output.

module Untyped.TypeInferenceEval
       (evalTypeInferenceResult)
where

import Prelude hiding(mapM)
import Control.Applicative
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

evCon :: CInst Untyped.TI -> IO (CInst SF)
evCon (Untyped.TIConInst con ty_args ex_types) =
  CInstSF <$> (VarCon con <$> mapM evType ty_args <*> mapM evType ex_types)

evExp :: Untyped.TIExp -> IO ExpSF
evExp expression =
  case expression
  of Untyped.RecVarPH {} -> getPlaceholderElaboration expression
     Untyped.DictPH {} -> getPlaceholderElaboration expression
     Untyped.TIExp e -> fmap ExpSF $
       case e
       of VarE info v ->
            return $ VarE info v
          LitE info l ->
            return $ LitE info l
          ConE info con args ->
            ConE info <$> evCon con <*> mapM evExp args
          AppE info op ts args ->
            AppE info <$> evExp op <*> mapM evTypSF ts <*> mapM evExp args
          LamE info f -> 
            LamE info <$> evFun f
          LetE info p r b ->
            LetE info <$> evPat p <*> evExp r <*> evExp b
          LetfunE info defs b ->
            LetfunE info <$> mapM evDef defs <*> evExp b
          CaseE info scr alts ->
            CaseE info <$> evExp scr <*> mapM evAlt alts
          CoerceE info from_t to_t b ->
            CoerceE info <$> evTypSF from_t <*> evTypSF to_t <*> evExp b
     Untyped.TIRecExp e ->
       return e

evAlt (Untyped.TIAlt (Alt decon params body)) = do
  decon' <- evDecon decon
  body' <- evExp body
  params' <- mapM evPat params
  return $ AltSF $ Alt decon' params' body'

evDecon (Untyped.TIDeConInst con ty_args ex_types) = do 
  ty_args' <- mapM evType ty_args
  ex_types' <- mapM evTyParam ex_types
  return $ DeCInstSF $ VarDeCon con ty_args' [b | TyPatSF b <- ex_types']

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
