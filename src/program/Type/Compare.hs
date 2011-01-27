
{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances #-}
module Type.Compare
       (typeMentions,
        typeMentionsAny,
        compareTypes,
        unifyTypeWithPattern
       )
where

import Control.Monad.Reader
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap

import Common.Identifier
import Common.MonadLogic
import Common.SourcePos
import Common.Supply
import Type.Environment
import Type.Rename
import Type.Type

-- | Determine whether the type mentions a variable.
--   It's assumed that name shadowing does /not/ occur.  If a variable is
--   defined somewhere inside the type and then used, that counts as a mention.
--   
typeMentions :: Type -> Var -> Bool
typeMentions t target = search t
  where
    search (VarT v) = v == target
    search (AppT op arg) = search op || search arg
    search (FunT (_ ::: dom) (_ ::: rng)) = search dom || search rng

-- | Determine whether the type mentions a variable in the set.
--   It's assumed that name shadowing does /not/ occur.  If a variable is
--   defined somewhere inside the type and then used, that counts as a mention.
--   
typeMentionsAny :: Type -> Set.Set Var -> Bool
typeMentionsAny t target = search t
  where
    search (VarT v) = v `Set.member` target
    search (AppT op arg) = search op || search arg
    search (FunT (_ ::: dom) (_ ::: rng)) = search dom || search rng

-------------------------------------------------------------------------------

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

-- | Given an expected type @t_e@, a set of flexible variables @fv$, and a
--   given type @t_g@, try to construct a unifying substitution
--   @S : fv -> Type@ such that @S(t_e) = t_g@.  The substitution applied to
--   the expected type makes it equal to the given type.
unifyTypeWithPattern :: IdentSupply Var
                     -> TypeEnv
                     -> [Var]   -- ^ Free variables in expected type
                     -> Type    -- ^ Expected type
                     -> Type    -- ^ Given type
                     -> IO (Maybe Substitution)
unifyTypeWithPattern id_supply _ free_vars expected given =
  runFreshVarM id_supply calculate_substitution
  where
    calculate_substitution = do
      result <- unify init_substitution expected given
      return $ case result
               of Just sub -> Just $ substitutionFromMap $ IntMap.mapMaybe id sub
                  Nothing -> Nothing

    init_substitution = IntMap.fromList [(fromIdent $ varID v, Nothing)
                                        | v <- free_vars]

-- | A substitution used in unification.  All flexible variables are in
--   the substitution.  If they haven't been assigned a value, their
--   value in the map is 'Nothing'.
type USubst = IntMap.IntMap (Maybe Type)

-- | Search for a substitution that unifies @expected@ with @given@.
--   Return a unifying substition if found.
unify :: USubst -> Type -> Type -> FreshVarM (Maybe USubst)
unify subst expected given = do
  -- Rename 'expected' so that bound variables match
  (given', expected') <- leftUnifyBoundVariables given expected
  match_unify expected' given'
  where
    no_unifier   = return Nothing
    unified_by s = return (Just s)

    -- Run two unification tasks sequentially
    unify2 s (e1, e2) (g1, g2) = do
      result1 <- unify s e1 g1
      case result1 of
        Just s' -> unify s' e2 g2
        Nothing -> no_unifier

    match_unify (VarT v) given =
      case IntMap.lookup (fromIdent $ varID v) subst
      of Just (Just v_value) ->
           -- v has been assigned a value; substitute it
           unify subst v_value given
         Just Nothing -> 
           -- v is flexible; assign it and succeed
           unified_by $ IntMap.insert (fromIdent $ varID v) (Just given) subst
         Nothing ->
           -- v is rigid; must be equal to 'given'
           case given
           of VarT v' | v == v' -> unified_by subst
              _ -> no_unifier

    match_unify (AppT t1 t2) (AppT t3 t4) =
      unify2 subst (t1, t2) (t3, t4)

    match_unify (FunT (r1 ::: t1) (r2 ::: t2)) (FunT (r3 ::: t3) (r4 ::: t4))
      | sameParamRepr r1 r3 && sameReturnRepr r2 r4 =
          unify2 subst (t1, t2) (t3, t4)
      | otherwise = no_unifier
       
    match_unify _ _ = no_unifier
