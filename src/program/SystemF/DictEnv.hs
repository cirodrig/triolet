{-| Dictionary environments.

The value of a class dictionary is completely determined by its type.  So,
to look for a class dictionary, we look for a variable that has the right type.
Dictionary environments hold mappings from types to values.

This module is meant to be imported qualified.
-}

{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
module SystemF.DictEnv where

import Text.PrettyPrint.HughesPJ
import Common.SourcePos
import Common.Supply
import Common.Identifier
import Type.Compare
import Type.Environment
import Type.Substitute(TypeSubst)
import qualified Type.Substitute as Substitute
import Type.Type

-- | A first-order pattern that can be matched against types
data TypePattern a = TypePattern [Var] Type (TypeSubst -> a)

monoPattern :: Type -> a -> TypePattern a
monoPattern t v = TypePattern [] t (\_ -> v)

pattern :: [Var] -> Type -> (TypeSubst -> a) -> TypePattern a
pattern = TypePattern

pattern1 :: (Monad m, Supplies m VarID) =>
            (Var -> (Type, TypeSubst -> a))
         -> m (TypePattern a)
pattern1 f = do
  v1 <- newAnonymousVar TypeLevel
  case f v1 of (k, v) -> return $ pattern [v1] k v

pattern2 :: (Monad m, Supplies m VarID) =>
            (Var -> Var -> (Type, TypeSubst -> a))
         -> m (TypePattern a)
pattern2 f = do
  v1 <- newAnonymousVar TypeLevel
  v2 <- newAnonymousVar TypeLevel
  case f v1 v2 of (k, v) -> return $ pattern [v1, v2] k v

newtype DictEnv a = DictEnv [TypePattern a]

empty :: DictEnv a
empty = DictEnv []

insert :: TypePattern a -> DictEnv a -> DictEnv a
insert p (DictEnv ps) = DictEnv (p : ps)

-- | Insert a pattern at the end of the environment.  The pattern will be
--   superseded by any previously inserted patterns.
insertAtEnd :: TypePattern a -> DictEnv a -> DictEnv a
insertAtEnd p (DictEnv ps) = DictEnv (ps ++ [p])

lookup :: EvalMonad m => Type -> DictEnv a -> m (Maybe a)
lookup key (DictEnv xs) = go xs
  where
    go (TypePattern qvars t mk_value : xs) = do
      -- Try to match 'key' against this pattern
      match <- unifyTypeWithPattern qvars t key
      case match of
        Nothing     -> go xs
        Just subst -> return (Just $ mk_value subst)
    
    go [] = return Nothing
