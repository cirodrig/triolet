
{-# LANGUAGE FlexibleContexts, TypeSynonymInstances #-}
module Type.Var
       (Var, varID, varName, 
        VarID,
        pprVar,
        mkVar, mkAnonymousVar,
        newVar, newAnonymousVar)
where

import Text.PrettyPrint.HughesPJ

import Gluon.Common.Identifier
import Gluon.Common.Supply
import Gluon.Core.Level
import LowLevel.Label

-- | A variable or constructor.
--
-- Each 'Var' has a unique identifier.  If two variables have the same
-- identifier, their other fields are equal.
data Var =
  Var { _varID :: {-# UNPACK #-} !(Ident Var)
      , _varName :: !(Maybe Label)
      , _varLevel :: !Level
      }

instance Eq Var where
  v1 == v2 = _varID v1 == _varID v2
  v1 /= v2 = _varID v1 /= _varID v2

instance Ord Var where
  compare v1 v2 = compare (_varID v1) (_varID v2)

instance Show Var where
  show v =
    let name = case _varName v
               of Nothing -> "_"
                  Just lab -> case labelLocalName lab
                              of Left str -> str
                                 Right (LocalID n) -> show n
    in name ++ "'" ++ show (fromIdent $ _varID v)

instance HasLevel Var where
  getLevel v = _varLevel v

type VarID = Ident Var
  
varID :: Var -> Ident Var
varID = _varID

varName :: Var -> Maybe Label
varName = _varName

mkVar :: VarID -> Maybe Label -> Level -> Var
mkVar = Var

mkAnonymousVar :: VarID -> Level -> Var
mkAnonymousVar id lv = mkVar id Nothing lv

newVar :: (Monad m, Supplies m VarID) => Maybe Label -> Level -> m Var
newVar lab lv = do
  id <- fresh
  return $ mkVar id lab lv

newAnonymousVar :: (Monad m, Supplies m VarID) => Level -> m Var
newAnonymousVar lv = newVar Nothing lv

pprVar :: Var -> Doc
pprVar v = text (show v)