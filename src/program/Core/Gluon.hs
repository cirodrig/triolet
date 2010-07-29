
module Core.Gluon
       (coreToGluonType, coreToGluonTypeWithoutEffects)
where
  
import Control.Monad

import Gluon.Common.Error
import Gluon.Core
import qualified Gluon.Core.Builtins.Effect
import Gluon.Eval.Environment
import Gluon.Eval.Eval
import SystemF.Builtins
import Core.Syntax

addressType = mkInternalConE (builtin the_Addr)
pointerType a = mkInternalConAppE (pyonBuiltin the_Ptr) [a]
ownedType ty = mkInternalConAppE (pyonBuiltin the_Own) [ty]
actionType e r = mkInternalConAppE (pyonBuiltin the_Action) [e, r]
stateType t a =
  let st = mkInternalConAppE (pyonBuiltin the_Def) [t]
  in mkInternalConAppE (builtin the_AtS) [a, st]
undefStateType t a =
  let st = mkInternalConAppE (pyonBuiltin the_Undef) [t]
  in mkInternalConAppE (builtin the_AtS) [a, st]

-- | Convert a core type to an equivalent Gluon type.
coreToGluonType :: EvalMonad m => RecCType SubstRec -> m RExp
coreToGluonType x = convertType True =<< freshenHead x

-- | Convert a core type to an equivalent Gluon type, with all
-- side effects removed from function types appearing in the type.
coreToGluonTypeWithoutEffects :: EvalMonad m => RecCType SubstRec -> m RExp
coreToGluonTypeWithoutEffects x = convertType False =<< freshenHead x

-- | Convert a core type to an equivalent Gluon type.
convertType :: EvalMonad m => Bool -> CType SubstRec -> m RExp
convertType have_effects ty =
  case ty of
    ExpCT e -> return $ substFully e
    AppCT op args -> do
      op' <- convertType have_effects =<< freshenHead op
      args' <- mapM (convertType have_effects <=< freshenHead) args
      return $ mkInternalAppE op' args'
    FunCT ft -> convertFunctionType have_effects =<< freshenHead ft

-- | Convert a core function type to an equivalent Gluon type.
--
-- All function types are converted to a function + monad type.
convertFunctionType :: EvalMonad m => Bool -> CFunType SubstRec -> m RExp
convertFunctionType have_effects (ArrCT (param ::: c_param_type) eff rng) = do
  g_param_type <- convertType have_effects =<< freshenHead c_param_type
  g_rng <- convertReturnType have_effects eff =<< freshenHead rng
  case param of
    ValPT mv -> do
      return $! case mv
                of Nothing -> mkInternalArrowE False g_param_type g_rng
                   Just v  -> mkInternalFunE False v g_param_type g_rng

    OwnPT -> do
      rng' <- convertReturnType have_effects eff =<< freshenHead rng
      return $ mkInternalArrowE False (ownedType g_param_type) g_rng

    ReadPT addr -> do
      return $ mkInternalFunE False addr addressType $
        mkInternalArrowE False (pointerType $ mkInternalVarE addr) g_rng

-- Should already be handled by 'convertReturnType'
convertFunctionType _ (RetCT _) = internalError "convertFunctionType"

convertReturnType :: EvalMonad m =>
                     Bool               -- ^ Generate side effects?
                  -> RecCType SubstRec  -- ^ Effect type
                  -> CFunType SubstRec  -- ^ Codomain
                  -> m RExp             -- ^ Converted type
convertReturnType have_effects eff range = do
  g_eff <- if have_effects
           then coreToGluonType eff
           else return Gluon.Core.Builtins.Effect.empty
  case range of
    ArrCT {} -> do
      range' <- convertFunctionType have_effects range
      return $ actionType g_eff range'
    RetCT (rparam ::: rtype) -> do
      g_rtype <- convertType have_effects =<< freshenHead rtype
      case rparam of
        ValRT -> return $ actionType g_eff g_rtype 
        OwnRT -> return $ actionType g_eff (ownedType g_rtype)
        WriteRT -> do
          addr_var <- newAnonymousVariable ObjectLevel
          let addr = mkInternalVarE addr_var
          return $
            mkInternalFunE False addr_var addressType $
            mkInternalArrowE False (pointerType addr) $
            mkInternalArrowE False (undefStateType g_rtype addr) $
            actionType g_eff (stateType g_rtype addr)
        ReadRT addr ->
          return $
          actionType g_eff $ pointerType (substFully addr)
       
  
  

