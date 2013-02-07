{-| Convert type-inferred expressions to System F.
    This pass over the program looks up the final values of
    placeholders and unification variables computed by type inference.
-}
module Untyped.TypeInferenceEval
       (evalTypeInferenceResult)
where

import Prelude hiding(mapM)
import Control.Applicative
import Control.Concurrent.MVar
import Control.Monad hiding(mapM)
import Control.Monad.Trans
import Data.IORef
import Data.Traversable(mapM)

import Common.Error
import Common.Label
import Common.Identifier
import Common.Supply
import Builtins.Builtins
import SystemF.Syntax
import Type.Type
import qualified Untyped.TIExp as U
import Untyped.TIExp(TIType, TIConInst, TIDeConInst, TITyPat, TIPat, TIExp,
                    TIFun, TIDef, TIAlt, TIExport)
import Untyped.TIMonad
import Untyped.Proof
import Globals

evType :: TIType -> TE Type
evType (U.DelayedType m) = m

evTyParam :: TITyPat -> TE TyPat
evTyParam (U.TITyPat v t) = do
  t' <- evType t
  return (TyPat (v ::: t'))

evPats = mapM evPat

evPat :: TIPat -> TE PatSF
evPat (U.TIVarP v t) = VarP v <$> evType t

evCon :: TIConInst -> TE ConInst
evCon (U.TIConInst con ty_args ex_types) =
  VarCon con <$> mapM evType ty_args <*> mapM evType ex_types

evExp :: TIExp -> TE ExpSF
evExp expression =
  case expression
  of U.VarTE info v ->
       return $ ExpSF $ VarE info v
     U.LitTE info l ->
       return $ ExpSF $ LitE info l
     U.ConTE info con _ args ->
       ExpSF <$> (ConE info <$> evCon con <*> mapM evExp args)
     U.AppTE info op ts args ->
       ExpSF <$> (AppE info <$> evExp op <*> mapM evType ts <*>
                  mapM evExp args)
     U.LamTE info f -> 
       ExpSF <$> (LamE info <$> evFun f)
     U.LetTE info p r b ->
       ExpSF <$> (LetE info <$> evPat p <*> evExp r <*> evExp b)
     U.LetfunTE info defs b ->
       ExpSF <$> (LetfunE info <$> mapM evDef defs <*> evExp b)
     U.CaseTE info scr _ alts ->
       ExpSF <$> (CaseE info <$> evExp scr <*> mapM (evAlt info) alts)
     U.CoerceTE info from_t to_t b ->
       ExpSF <$> (CoerceE info <$> evType from_t <*> evType to_t <*> evExp b)
     U.ArrayTE info t es ->
       ExpSF <$> (ArrayE info <$> evType t <*> mapM evExp es)
     U.PlaceholderTE ph ->
       evExp =<< evPlaceholder ph
     
evPlaceholder (U.DictPlaceholder (U.DictP prd ref)) = do
  v <- readPlaceholderValue ref
  return $ proofExp prd v
evPlaceholder (U.RecVarPlaceholder (U.RecVarP _ ref)) = readPlaceholderValue ref

readPlaceholderValue ref = do
  m_exp <- liftIO $ readIORef ref
  case m_exp of
    Just e  -> return e
    Nothing -> internalError "Placeholder not assigned"

evAlt info (U.TIAlt decon params body) =
  AltSF <$> (Alt <$> evDecon decon <*> evPats params <*> evExp body)

evDecon (U.TIDeConInst con ty_args ex_types) = do 
  ty_args' <- mapM evType ty_args
  ex_types' <- mapM evTyParam ex_types
  return $ VarDeCon con ty_args' [b | TyPat b <- ex_types']

evFun :: TIFun -> TE FunSF
evFun (U.TIFun inf ty_params params rt body) = do
  ty_params' <- mapM evTyParam ty_params
  FunSF <$> (Fun (mkExpInfo inf) ty_params' <$>
             evPats params <*> evType rt <*> evExp body)

evDef :: TIDef -> TE (FDef SF)
evDef (U.TIDef v ann f) = Def v ann <$> evFun f

evGlobalDef :: TIDef -> TE (GDef SF)
evGlobalDef (U.TIDef v ann f) = Def v ann <$> (FunEnt <$> evFun f)

evExport :: TIExport -> TE (Export SF)
evExport (U.TIExport pos spec f) =
  Export pos spec <$> evFun f

evalTypeInferenceResult :: (ModuleName, [DefGroup TIDef], [TIExport])
                        -> TE (Module SF)
evalTypeInferenceResult (module_name, defs, exports) = do
  defs' <- mapM (mapM evGlobalDef) defs
  exports' <- mapM evExport exports
  return $ Module module_name [] defs' exports'
