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
import Common.Identifier
import Common.Supply
import Builtins.Builtins
import SystemF.Syntax
import Type.Type
import qualified Untyped.Data as U
import Untyped.Data(TIType, TIConInst, TIDeConInst, TITyPat, TIPat, TIExp,
                    TIFun, TIDef, TIAlt, TIExport)
import Globals

evNewVar :: Maybe Label -> Level -> IO Var
evNewVar lab lv = do
  var_id <- withTheNewVarIdentSupply supplyValue
  return $ mkVar var_id Nothing ObjectLevel

evType :: TIType -> IO Type
evType (U.DelayedType m) = m

evTyParam :: TITyPat -> IO TyPat
evTyParam (U.TITyPat v t) = do
  t' <- evType t
  return (TyPat (v ::: t'))

evPats :: ExpInfo -> [TIPat] -> IO ([PatSF], ExpSF -> ExpSF)
evPats inf ps = do
  (ps', contexts) <- mapAndUnzipM (evPat inf) ps
  return (ps', \e -> foldr ($) e contexts)

-- | Convert pattern matching to simple variable bindings and case statements.
evPat :: ExpInfo -> TIPat -> IO (PatSF, ExpSF -> ExpSF)
evPat inf pat =
  case pat
  of U.TIWildP t -> do
       -- Create a pattern variable
       var <- evNewVar Nothing ObjectLevel
       ty <- evType t
       return (VarP var ty, id)

     U.TIVarP v t -> do
       ty <- evType t
       return (VarP v ty, id)

     U.TITupleP ps -> do
       (field_patterns, contexts) <- evPats inf ps
       let field_types = [ty | VarP _ ty <- field_patterns]
           tuple_size = length field_types
           tuple_tycon = pyonTupleTypeCon tuple_size
           tuple_type = varApp tuple_tycon field_types
           tuple_con = pyonTupleCon tuple_size
           tuple_decon = VarDeCon tuple_con field_types []

       -- Create a variable to bind the tuple value.
       -- Generate a case statement to deconstruct it.
       var <- evNewVar Nothing ObjectLevel
       let make_case body =
             ExpSF $ CaseE inf (ExpSF $ VarE inf var)
             [AltSF $ Alt tuple_decon field_patterns (contexts body)]
       
       return (VarP var tuple_type, make_case)

evCon :: TIConInst -> IO ConInst
evCon (U.TIConInst con ty_args ex_types) =
  VarCon con <$> mapM evType ty_args <*> mapM evType ex_types

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
       ExpSF <$> (AppE info <$> evExp op <*> mapM evType ts <*>
                  mapM evExp args)
     U.LamTE info f -> 
       ExpSF <$> (LamE info <$> evFun f)
     U.LetTE info p r b -> do
       (binder, body_context) <- evPat info p
       r' <- evExp r
       b' <- evExp b
       return $ ExpSF $ LetE info binder r' (body_context b')
     U.LetfunTE info defs b ->
       ExpSF <$> (LetfunE info <$> mapM evDef defs <*> evExp b)
     U.CaseTE info scr alts ->
       ExpSF <$> (CaseE info <$> evExp scr <*> mapM (evAlt info) alts)
     U.CoerceTE info from_t to_t b ->
       ExpSF <$> (CoerceE info <$> evType from_t <*> evType to_t <*> evExp b)
     U.ArrayTE info t es ->
       ExpSF <$> (ArrayE info <$> evType t <*> mapM evExp es)
     U.RecVarPH {} -> getPlaceholderElaboration expression
     U.DictPH {} -> getPlaceholderElaboration expression

evAlt info (U.TIAlt decon params body) = do
  decon' <- evDecon decon
  (params', body_context) <- evPats info params
  body' <- evExp body
  return $ AltSF $ Alt decon' params' (body_context body')

evDecon (U.TIDeConInst con ty_args ex_types) = do 
  ty_args' <- mapM evType ty_args
  ex_types' <- mapM evTyParam ex_types
  return $ VarDeCon con ty_args' [b | TyPat b <- ex_types']

-- | Get the expression that was stored for a placeholder, and evaluate it
getPlaceholderElaboration ph = do
  is_empty <- isEmptyMVar $ U.phExpResolution ph
  when is_empty $ internalError "Unresolved placeholder"
  evExp =<< readMVar (U.phExpResolution ph)

evFun :: TIFun -> IO FunSF
evFun (U.TIFun inf ty_params params rt body) = do
  ty_params' <- mapM evTyParam ty_params
  (params', body_context) <- evPats inf params
  rt' <- evType rt
  body' <- evExp body
  return $ FunSF $ Fun inf ty_params' params' rt' (body_context body')

evDef :: TIDef -> IO (FDef SF)
evDef (U.TIDef v ann f) = Def v ann <$> evFun f

evGlobalDef :: TIDef -> IO (GDef SF)
evGlobalDef (U.TIDef v ann f) = Def v ann <$> (FunEnt <$> evFun f)

evExport :: TIExport -> IO (Export SF)
evExport (U.TIExport pos spec f) =
  Export pos spec `liftM` evFun f

evalTypeInferenceResult :: (ModuleName, [DefGroup TIDef], [TIExport])
                        -> IO (Module SF)
evalTypeInferenceResult (module_name, defs, exports) = do
  defs' <- mapM (mapM evGlobalDef) defs
  exports' <- mapM evExport exports
  return $ Module module_name [] defs' exports'
