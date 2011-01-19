
{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances #-}
module Type.Compare(sameParamRepr, sameReturnRepr, compareTypes)
where

import Control.Monad.Reader

import Gluon.Common.Identifier
import Gluon.Common.MonadLogic
import Gluon.Common.SourcePos
import Gluon.Common.Supply
import Type.Environment
import Type.Rename
import Type.Type
import Type.Var

-- | True if the given representations are the same, False otherwise.
--   Parameter variables are ignored.
sameParamRepr :: ParamRepr -> ParamRepr -> Bool
sameParamRepr (ValPT _) (ValPT _) = True
sameParamRepr BoxPT     BoxPT     = True 
sameParamRepr ReadPT    ReadPT    = True 
sameParamRepr WritePT   WritePT   = True 
sameParamRepr _         _         = False

-- | True if the given representations are the same, False otherwise.
sameReturnRepr :: ReturnRepr -> ReturnRepr -> Bool
sameReturnRepr ValRT     ValRT     = True
sameReturnRepr BoxRT     BoxRT     = True 
sameReturnRepr ReadRT    ReadRT    = True 
sameReturnRepr WriteRT   WriteRT   = True 
sameReturnRepr _         _         = False

data CmpEnv =
  CmpEnv
  { reason :: SourcePos         -- ^ Reason for comparing types
  , varIDSupply :: !(IdentSupply Var) -- ^ Variable ID supply
  , typeEnv :: TypeEnv          -- ^ The current type environment
  }

newtype CmpM a = CmpM (ReaderT CmpEnv IO a) deriving(Monad)

instance Supplies CmpM (Ident Var) where
  fresh = CmpM $ ReaderT $ \env -> supplyValue $ varIDSupply env

runCmpM (CmpM m) id_supply pos env =
  runReaderT m (CmpEnv pos id_supply env)

-- | Compare two types.  Return True if the given type is equal to or a subtype
--   of the expected type, False otherwise.
compareTypes :: IdentSupply Var
             -> SourcePos       -- ^ Reason for comparing types
             -> TypeEnv         -- ^ Initial type environment
             -> Type            -- ^ Expected type
             -> Type            -- ^ Given Type
             -> IO Bool
compareTypes id_supply pos env expected given =
  runCmpM (cmpType expected given) id_supply pos env

cmpType :: Type -> Type -> CmpM Bool
cmpType expected given = cmp =<< unifyBoundVariables expected given
  where
    cmp (VarT v1, VarT v2) = return $ v1 == v2
    cmp (AppT op1 arg1, AppT op2 arg2) = cmpType op1 op2 >&&> cmpType arg1 arg2
    cmp (FunT (arg1 ::: dom1) result1, FunT (arg2 ::: dom2) result2) =
      cmpType dom1 dom2 >&&> cmpFun arg1 arg2 dom2 result1 result2

    cmp (_, _) = return False

    cmpFun arg1 arg2 dom result1 result2
      | sameParamRepr arg1 arg2 = cmpReturns result1 result2
      | otherwise               = return False

cmpReturns :: ReturnRepr ::: Type -> ReturnRepr ::: Type -> CmpM Bool
cmpReturns (ret1 ::: rng1) (ret2 ::: rng2)
  | sameReturnRepr ret1 ret2 = cmpType rng1 rng2
  | otherwise = return False

