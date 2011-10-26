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
import Common.Label
import SystemF.Syntax
import Type.Type
import qualified Untyped.Data as U
import Untyped.Data(TIType, TIConInst, TIDeConInst, TITyPat, TIPat, TIExp,
                    TIFun, TIDef, TIAlt, TIExport)

evTypSF :: TIType -> IO TypSF
evTypSF (U.DelayedType m) = fmap TypSF m

evType :: TIType -> IO Type
evType (U.DelayedType m) = m

evTyParam :: TITyPat -> IO (TyPat SF)
evTyParam (U.TITyPat v t) = do
  t' <- evType t
  return (TyPatSF (v ::: t'))

evPat :: TIPat -> IO PatSF
evPat (U.TIWildP t)   = WildP `liftM` evType t
evPat (U.TIVarP v t)  = VarP v `liftM` evType t
evPat (U.TITupleP ps) = TupleP `liftM` mapM evPat ps

evCon :: TIConInst -> IO (CInst SF)
evCon (U.TIConInst con ty_args ex_types) =
  CInstSF <$> (VarCon con <$> mapM evType ty_args <*> mapM evType ex_types)

evExp :: TIExp -> IO ExpSF
evExp expression =
  case expression
  of U.VarTE info v ->
       return $ ExpSF $ VarE info v
     U.LitTE info l ->
       return $ ExpSF $ LitE info l
     U.ConTE info con args ->
       ExpSF <$> (ConE info <$> evCon con <*> mapM evExp args)
     U.AppTE info op ts args ->
       ExpSF <$> (AppE info <$> evExp op <*> mapM evTypSF ts <*> mapM evExp args)
     U.LamTE info f -> 
       ExpSF <$> (LamE info <$> evFun f)
     U.LetTE info p r b ->
       ExpSF <$> (LetE info <$> evPat p <*> evExp r <*> evExp b)
     U.LetfunTE info defs b ->
       ExpSF <$> (LetfunE info <$> mapM evDef defs <*> evExp b)
     U.CaseTE info scr alts ->
       ExpSF <$> (CaseE info <$> evExp scr <*> mapM evAlt alts)
     U.CoerceTE info from_t to_t b ->
       ExpSF <$> (CoerceE info <$> evTypSF from_t <*> evTypSF to_t <*> evExp b)
     U.RecVarPH {} -> getPlaceholderElaboration expression
     U.DictPH {} -> getPlaceholderElaboration expression

evAlt (U.TIAlt decon params body) = do
  decon' <- evDecon decon
  body' <- evExp body
  params' <- mapM evPat params
  return $ AltSF $ Alt decon' params' body'

evDecon (U.TIDeConInst con ty_args ex_types) = do 
  ty_args' <- mapM evType ty_args
  ex_types' <- mapM evTyParam ex_types
  return $ DeCInstSF $ VarDeCon con ty_args' [b | TyPatSF b <- ex_types']

-- | Get the expression that was stored for a placeholder, and evaluate it
getPlaceholderElaboration ph = do
  is_empty <- isEmptyMVar $ U.phExpResolution ph
  when is_empty $ internalError "Unresolved placeholder"
  evExp =<< readMVar (U.phExpResolution ph)

evFun :: TIFun -> IO FunSF
evFun (U.TIFun inf ty_params params rt body) =
  FunSF <$> (Fun inf <$> mapM evTyParam ty_params <*> mapM evPat params <*>
             evTypSF rt <*> evExp body)

evDef :: TIDef -> IO (Def SF)
evDef (U.TIDef v ann f) = Def v ann <$> evFun f

evExport :: TIExport -> IO (Export SF)
evExport (U.TIExport pos spec f) = Export pos spec `liftM` evFun f

evalTypeInferenceResult :: (ModuleName, [DefGroup TIDef], [TIExport])
                        -> IO (Module SF)
evalTypeInferenceResult (module_name, defs, exports) = do
  defs' <- mapM (mapM evDef) defs
  exports' <- mapM evExport exports
  return $ Module module_name [] defs' exports'
