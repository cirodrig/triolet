{-| Convert type-inferred expressions to System F.
    This pass over the program looks up the final values of
    placeholders and unification variables computed by type inference.
-}
module Untyped.TypeInferenceEval
       (evalTypeInferenceResult)
where

import Prelude hiding(mapM)
import Control.Applicative
import Control.DeepSeq
import Control.Concurrent.MVar
import Control.Monad hiding(mapM)
import Control.Monad.Trans
import Data.IORef
import Data.Traversable(mapM)

import Common.Error
import Common.Label
import Common.Identifier
import Common.SourcePos
import Common.Supply
import Builtins.Builtins
import SystemF.Syntax
import SystemF.Print
import Type.Type
import qualified Untyped.TIExp as U
import Untyped.TIExp(TIType, TIConInst, TIDeConInst, TITyPat, TIPat, TIExp,
                    TIFun, TIDef, TIAlt, TIExport)
import Untyped.TIMonad
import Untyped.Proof
import Globals

-- | For debugging: reduce to normal form
db_rnf :: NFData a => a -> TE a
db_rnf x = rnf x `seq` return x

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

evExpInfo :: U.TIInfo -> TE ExpInfo
evExpInfo (U.TIInfo pos r) = mkExpInfoWithRepresentation pos <$> evRepr pos r

evRepr :: SourcePos -> U.TIRepr -> TE Representation
evRepr pos U.TIBoxed = return BoxedRepresentation
evRepr pos U.TIUncoercedVal = return ValueRepresentation
evRepr pos (U.TIInferredRepr e) = Representation <$> evExp e
evRepr pos (U.TICoreRepr op ty_args args) =
  mk_app op <$> mapM evType ty_args <*> mapM ev_arg args
  where
    ev_arg (Left e) = evExp e
    ev_arg (Right r) = do r' <- evRepr pos r
                          case r' of Representation e -> return e
                                     _ -> internalError "evRepr"

    mk_app op ty_args args =
      let op_exp = ExpSF (VarE (mkExpInfoWithRepresentation pos BoxedRepresentation) op)
          info = mkExpInfoWithRepresentation pos BoxedRepresentation
      in Representation $ ExpSF (AppE info op_exp ty_args args)

-- | Convert a 'Repr' to an expression that evaluates to run-time type info
evReprExp :: SourcePos -> U.TIRepr -> TE ExpSF
evReprExp pos repr = evRepr pos repr >>= as_exp
  where
    as_exp BoxedRepresentation = undefined
    as_exp ValueRepresentation = undefined
    as_exp (Representation e) = return e

-- | Convert a 'Size' to an expression that evaluates to a run-time size.
--   Returns the size and run-time type info.
evSizeExp :: SourcePos -> U.TISize -> TE (ExpSF, ExpSF)
evSizeExp pos (U.TISize ty repr) = do
  repr' <- evReprExp pos repr
  ty' <- evType ty
  return (size_expression ty' repr', repr')
  where
    size_expression t e = ExpSF $ AppE size_info size_op [t] [e]
    size_info = mkExpInfoWithRepresentation pos ValueRepresentation
    size_op = ExpSF $ VarE (mkExpInfoWithRepresentation pos BoxedRepresentation)
                           (coreBuiltin The_reprSizeAlign)

evExp :: TIExp -> TE ExpSF
evExp expression =
  case expression
  of U.VarTE info v -> do
       info' <- evExpInfo info
       return $ ExpSF $ VarE info' v
     U.LitTE info l -> do
       info' <- evExpInfo info
       return $ ExpSF $ LitE info' l
     U.ConTE info con sps m_tyob_con args -> do
       let U.TIInfo pos _ = info
       info' <- evExpInfo info
       con' <- evCon con
       (sizes, sps') <- mapAndUnzipM (evSizeExp pos) sps
       args' <- mapM evExp args

       -- If there is a type object constructor function,
       -- apply it to the type parameters, existential types,
       -- and size parameters.  The result is boxed.
       let tyob = do
             op <- m_tyob_con
             let info = mkExpInfoWithRepresentation pos BoxedRepresentation
                 op_exp = ExpSF $ VarE info op
                 ty_args = case con'
                           of VarCon _ ty_args ex_types -> ty_args ++ ex_types
                              TupleCon ts -> ts
             return $ ExpSF $ AppE info op_exp ty_args sps'
       return $ ExpSF $ ConE info' con' sizes tyob args'
     U.AppTE info op ts args ->
       ExpSF <$> (AppE <$> evExpInfo info <*> evExp op <*> mapM evType ts <*>
                  mapM evExp args)
     U.LamTE info f ->
       ExpSF <$> (LamE <$> evExpInfo info <*> evFun f)
     U.LetTE pos p r b ->
       ExpSF <$> (LetE (mkExpInfo pos) <$> evPat p <*> evExp r <*> evExp b)
     U.LetfunTE pos defs b ->
       ExpSF <$> (LetfunE (mkExpInfo pos) <$> mapM evDef defs <*> evExp b)
     U.CaseTE pos scr sps alts ->
       ExpSF <$> (CaseE (mkExpInfo pos) <$> evExp scr <*>
                  mapM (fmap fst . evSizeExp pos) sps <*>
                  mapM (evAlt pos) alts)
     U.CoerceTE info from_t to_t b ->
       ExpSF <$> (CoerceE <$> evExpInfo info <*>
                  evType from_t <*> evType to_t <*> evExp b)
     U.ArrayTE info t es ->
       ExpSF <$> (ArrayE <$> evExpInfo info <*> evType t <*> mapM evExp es)
     U.MkExpTE info f ts es ->
       f <$> mapM evType ts <*> mapM evExp es
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

evAlt pos (U.TIAlt decon type_object_param params body) = do
  ty_pat <- case type_object_param
            of Nothing -> return Nothing
               Just ty -> do
                 v <- newAnonymousVar ObjectLevel
                 ty' <- evType ty
                 let tyob_type = boxInfoT `AppT` ty'
                 return $ Just $ VarP v tyob_type
  AltSF <$> (Alt <$> evDecon decon <*> pure ty_pat <*>
             evPats params <*> evExp body)

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
