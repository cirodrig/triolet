
{-# LANGUAGE TypeFamilies, DeriveDataTypeable #-}
module Pyon.Untyped.HMType
       (Substitution, substitutionFromList,
        TyVars, TyVarSet, TyCon,
        tyConKind, tyConPassConv, tyConPassConvCtor, tyConPassConvArgs, 
        tyConExecMode,
        isTyVar, isRigidTyVar, isFlexibleTyVar,
        isCanonicalTyVar,
        newTyVar, newRigidTyVar, mkTyCon, duplicateTyVar,
        HMType(..),
        appTy,
        tupleType, functionType,
        uncurryTypeApplication,
        inspectTypeApplication,
        hmTypeKind,
        hmTypeMap, hmTypeMapM,
        canonicalizeHead,
        Type(..),
        unifiableTypeVariables,
        Unifiable(..),
        tyVarToSystemF,
        tyConToSystemF
       )
where

import Prelude hiding(sequence)
import Control.Applicative
import Control.Monad hiding(sequence)
import Control.Monad.Trans
import Data.Function
import Data.IORef
import Data.List
import Data.Traversable
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe
import Debug.Trace
import System.IO.Unsafe
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.MonadLogic
import Gluon.Common.SourcePos
import Gluon.Common.Supply
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Core(Var(..), mkVar, Level(..), Rec, Con)

import Pyon.Globals
import qualified Pyon.SystemF.Syntax as SystemF
import Pyon.Untyped.Data
import Pyon.Untyped.Kind
import Pyon.Untyped.Unification

tyConIDSupply :: Supply (Ident TyCon)
{-# NOINLINE tyConIDSupply #-}
tyConIDSupply = unsafePerformIO newIdentSupply

newTyConID :: IO (Ident TyCon)
newTyConID = supplyValue tyConIDSupply

tyConKind :: TyCon -> Kind
tyConKind = tcKind

isTyVar :: TyCon -> Bool
isTyVar = tcIsVariable

isRigidTyVar :: TyCon -> Bool
isRigidTyVar c = isTyVar c && isNothing (tcRep c)

isFlexibleTyVar :: TyCon -> Bool
isFlexibleTyVar c = isTyVar c && isJust (tcRep c)

-- | Get the parameter-passing convention of a type constructor
tyConPassConv :: TyCon -> PassConvCtor
tyConPassConv = tcPassConv . tcConInfo

-- | Get the proof constructor for a type constructor's parameter-passing
-- convention
tyConPassConvCtor :: TyCon -> Con
tyConPassConvCtor = tcPassConvProof . tcConInfo

-- | Get the parameter-passing convention proof arguments
tyConPassConvArgs :: TyCon -> [Bool]
tyConPassConvArgs = tcPassConvArgs . tcConInfo

-- | Get the execution mode of a type constructor
tyConExecMode :: TyCon -> ExecMode
tyConExecMode = tcExecMode . tcConInfo

-- | Create a new flexible type variable
newTyVar :: Kind -> Maybe Label -> IO TyCon
newTyVar k lab = do
  id <- newTyConID
  rep <- newIORef NoRep
  sfvar <- newIORef Nothing
  let con_descr = internalError 
                  "Type variables do not have constructor information"
  return $! TyCon id lab k True (Just rep) sfvar con_descr

-- | Create a new rigid type variable
newRigidTyVar :: Kind -> Maybe Label -> IO TyCon
newRigidTyVar k lab = do
  id <- newTyConID
  sfvar <- newIORef Nothing
  let con_descr = internalError
                  "Type variables do not have constructor information"
  return $! TyCon id lab k True Nothing sfvar con_descr

-- | Create a type constructor
mkTyCon :: Label -> Kind -> SystemF.RType -> PassConvCtor -> Con -> [Bool]
        -> ExecMode
        -> IO TyCon
mkTyCon name kind value pass_conv pass_conv_proof pass_conv_args em = do
  id <- newTyConID
  let var = error "Type constructor is not a variable"
      con_descr = TyConDescr
                  { tcSystemFValue = value
                  , tcPassConv = pass_conv
                  , tcPassConvProof = pass_conv_proof
                  , tcPassConvArgs = pass_conv_args
                  , tcExecMode = em
                  }
  return $! TyCon id (Just name) kind False Nothing var con_descr

-- | Create a new type variable that is like the given one, but independent
-- with respect to unification
duplicateTyVar :: TyCon -> IO TyCon
duplicateTyVar v = 
  case isTyVar v
  of True -> newTyVar (tcKind v) (tcName v)
     False -> fail "Expecting a type variable"

isNoRep NoRep = True
isNoRep _ = False

kindError = error "Kind error in type application"

-- | Apply a type of kind @k1 -> k2@ to a type of kind @k1@
appTy :: HMType -> HMType -> HMType
s `appTy` t =
  case hmTypeKind s
  of k :-> _ -> if hmTypeKind t == k then s `AppTy` t else kindError
     _       -> kindError

tupleType :: [HMType] -> HMType
tupleType ts 
  | any ((Star /=) . hmTypeKind) ts = kindError
  | otherwise = foldl AppTy (TupleTy $ length ts) ts

functionType :: [HMType] -> HMType -> HMType
functionType dom rng 
  | any ((Star /=) . hmTypeKind) dom = kindError 
  | Star /= hmTypeKind rng = kindError
  | otherwise = foldl AppTy (FunTy $ length dom) (dom ++ [rng])

hmTypeKind :: HMType -> Kind
hmTypeKind (ConTy c)     = tcKind c
hmTypeKind (FunTy n)     = nAryKind (n+1)
hmTypeKind (TupleTy n)   = nAryKind n
hmTypeKind (AppTy t1 t2) = case hmTypeKind t1
                           of _ :-> k -> k
                              Star    -> error "Kind error in type application"

hmTypeMap :: (HMType -> HMType) -> HMType -> HMType
hmTypeMap f t =
  case f t
  of AppTy t1 t2 -> hmTypeMap f t1 `appTy` hmTypeMap f t2
     t'          -> t'

hmTypeMapM :: (HMType -> IO HMType) -> HMType -> IO HMType
hmTypeMapM f t = do
  t' <- f t
  case t' of
    AppTy t1 t2 -> liftM2 appTy (hmTypeMapM f t1) (hmTypeMapM f t2)
    _ -> return t'

-- | Uncurry type applications, returning an operator and all arguments that 
-- it is applied to
uncurryTypeApplication :: HMType -> IO (HMType, [HMType])
uncurryTypeApplication ty = unc ty []
  where
    unc ty args = do
      ty' <- canonicalizeHead ty
      case ty' of
        AppTy op arg -> unc op (arg:args)
        _ -> return (ty', args)

-- | Get the head and operands of a type application.  The head constructor is
-- canonicalized.
inspectTypeApplication :: HMType -> IO (HMType, [HMType])
inspectTypeApplication ty = do
  (hd, operands) <- uncurryTypeApplication ty
  hd' <- canonicalizeHead hd
  return (hd', operands)

-- | Get the set of free and unifiable type variables mentioned in the value
unifiableTypeVariables :: Type a => a -> IO TyVarSet
unifiableTypeVariables t =
  liftM (Set.filter isFlexibleTyVar) $ freeTypeVariables t

instance Type HMType where
  freeTypeVariables t = do
    t' <- canonicalizeHead t
    case t' of
      ConTy c | isTyVar c -> return $ Set.singleton c
              | otherwise -> return $ Set.empty
      AppTy t1 t2 -> do s1 <- freeTypeVariables t1 
                        s2 <- freeTypeVariables t2
                        return $ Set.union s1 s2
      _ -> return Set.empty

-------------------------------------------------------------------------------
-- Unification

-- | Get a type variable's representative pointer.  Throw an error if the
-- parameter is not a flexible type variable.
getTyVarRep :: TyCon -> IORef TyVarRep
getTyVarRep c =
  case tcRep c
  of Nothing      -> error "Expecting a flexible type variable"
     Just rep_ref -> rep_ref

-- | Throw an error unless the variable is in canonical form
assertCanonicalTyVar :: TyCon -> IO ()
assertCanonicalTyVar v = do
  rep <- readIORef $ getTyVarRep v
  unless (isNoRep rep) $ fail "Expecting a canonical type variable" 

-- | Unify two type variables.  The type variables should be canonical.
unifyTyVars :: TyCon -> TyCon -> IO ()
unifyTyVars v1 v2 
  | v1 == v2 = return ()
  | tyConKind v1 /= tyConKind v2 = kindError
  | otherwise = do
      assertCanonicalTyVar v1
      assertCanonicalTyVar v2
      writeIORef (getTyVarRep v1) (TyVarRep v2)

-- | Unify a type variable with an expression.
-- If the variable is mentioned in the type 't', an error is raised.
-- The variable should be canonical.
unifyTyVar :: TyCon -> HMType -> IO ()
unifyTyVar v t 
  | tyConKind v /= hmTypeKind t = kindError
  | otherwise = do
  assertCanonicalTyVar v
  occursCheck v t
  writeIORef (getTyVarRep v) (TypeRep t)

-- | Convert a flexible type variable to a canonical expression
canonicalizeTyVar :: TyCon -> IO HMType
canonicalizeTyVar v = do
  return . makeType =<< canonicalizeTyVarRep (getTyVarRep v)
  where
    makeType NoRep         = ConTy v
    makeType (TyVarRep v') = ConTy v'
    makeType (TypeRep t)   = t

-- | Return True if the parameter has not been unified with anything.
-- The parameter must be a flexible type variable.
isCanonicalTyVar :: TyCon -> IO Bool
isCanonicalTyVar v = do
  rep <- readIORef $ getTyVarRep v
  return $ isNoRep rep

-- | Update a unifier pointer, removing indirections, and return 
-- its reduced form
canonicalizeTyVarRep :: IORef TyVarRep -> IO TyVarRep
canonicalizeTyVarRep rep_ref = do
  rep <- readIORef rep_ref
  case rep of
    NoRep      -> return rep
    TyVarRep v -> update_self rep =<< canonicalizeTyVarRep (getTyVarRep v)
    TypeRep t  -> return rep
  where
    update_self old_rep NoRep   = return old_rep
    update_self _       new_rep = do writeIORef rep_ref new_rep
                                     return new_rep

canonicalizeHead :: HMType -> IO HMType 
canonicalizeHead (ConTy v) 
  | isFlexibleTyVar v = canonicalizeTyVar v
canonicalizeHead t = return t

-- | Check whether a variable (which should be in canonical form) appears
-- in the type
occursCheck :: TyCon -> HMType -> IO Bool
occursCheck v t = do assertCanonicalTyVar v
                     occ t
  where
    occ t = do t_c <- canonicalizeHead t 
               case t_c of
                 ConTy v2  -> return $ v == v2
                 AppTy a b -> occ a >||> occ b
                 _ -> return False

instance Unifiable HMType where
  uShow = pprType

  rename substitution t = hmTypeMapM (ren <=< canonicalizeHead) t
    where
      -- Look up in substitution
      ren t@(ConTy v) | isTyVar v = 
        return $ Map.findWithDefault t v (substTc substitution)
      ren t = return t

  -- Unify types.  Unification on types never produces constraints.
  unify pos t1 t2 = do
    t1_c <- canonicalizeHead t1
    t2_c <- canonicalizeHead t2

    -- Unify if either term contains a type variable.
    case (t1_c, t2_c) of
      (ConTy c1, ConTy c2)   
        | isFlexibleTyVar c1 && isFlexibleTyVar c2 -> do unifyTyVars c1 c2
                                                         success
      (ConTy c1, _)
        | isFlexibleTyVar c1 -> do unifyTyVar c1 t2_c
                                   success
      (_, ConTy c2)
        | isFlexibleTyVar c2 -> do unifyTyVar c2 t1_c
                                   success
      (ConTy c1, ConTy c2)     -> require $ c1 == c2
      (FunTy n1,   FunTy n2)   -> require $ n1 == n2
      (TupleTy t1, TupleTy t2) -> require $ t1 == t2
      (AppTy a b,  AppTy c d)  -> do unify pos a c
                                     unify pos b d
      _ -> failure
    where
      success = return []
      failure = do
        (t1_doc, t2_doc) <- runPpr $ (,) <$> uShow t1 <*> uShow t2
        fail $ show (text (show pos) <> text ":" <+> text "Cannot unify" $$
                     nest 4 t1_doc $$
                     text "with" $$
                     nest 4 t2_doc)
      require True  = success
      require False = failure

  match t1 t2 = match_ emptySubstitution t1 t2
    where
      match_ subst t1 t2 = do
        t1_c <- canonicalizeHead t1
        t2_c <- canonicalizeHead t2
        
        case (t1_c, t2_c) of
          (ConTy v, _) | isFlexibleTyVar v ->
            -- Semi-unification of a variable with t2_c
            -- Look for this variable's value in the map
            case Map.lookup v (substTc subst)
            of Just substituted_t1 -> do
                 -- Match terms without further substitution
                 require =<< uEqual substituted_t1 t2_c
               Nothing ->
                 -- Add the mapping v |-> t2_c and succeed
                 let subst' = updateTc (Map.insert v t2_c) subst
                 in return (Just subst')
          
          -- Non-variable terms must match exactly
          (ConTy c1, ConTy c2) -> require $ c1 == c2
          (FunTy n1, FunTy n2) -> require $ n1 == n2
          (TupleTy t1, TupleTy t2) -> require $ t1 == t2
          -- Recurse on app terms
          (AppTy a b,  AppTy c d) -> do result1 <- match_ subst a c
                                        case result1 of
                                          Nothing -> return Nothing
                                          Just subst' -> match_ subst' b d
          _ -> failure
        where
          success = return (Just subst)
          failure = return Nothing
          require True  = success
          require False = failure
        
  uEqual t1 t2 = do
    t1_c <- canonicalizeHead t1
    t2_c <- canonicalizeHead t2
    
    case (t1_c, t2_c) of
      (ConTy c1,   ConTy c2)   -> return $ c1 == c2
      (FunTy n1,   FunTy n2)   -> return $ n1 == n2
      (TupleTy t1, TupleTy t2) -> return $ t1 == t2
      (AppTy a b,  AppTy c d)  -> uEqual a c >&&> uEqual b d
      _ -> return False
    
-------------------------------------------------------------------------------
-- Pretty-printing

-- precedences
outer_prec = 0
arrow_prec = 1
prod_prec = 2
app_prec = 4

pprType :: HMType -> Ppr Doc
pprType ty = prType 0 ty

prType :: Int -> HMType -> Ppr Doc
prType prec t = do
  -- Uncurry the type application and put the head in canonical form
  (hd, params) <- liftIO $ inspectTypeApplication t
  case hd of
    ConTy c -> application <$> conName c <*> traverse (prType app_prec) params
    FunTy n
      | n + 1 == length params ->
        let domain = sep . intersperse (text "*") <$>
                     traverse (prType prod_prec) (init params)
            range = prType arrow_prec $ last params
        in parenthesize arrow_prec <$> domain `arrow` range
      | otherwise ->
          application (parens (text ("FunTy " ++ show n))) <$>
          traverse (prType app_prec) params
    TupleTy n
      | n == length params ->
        parens . sep . punctuate (text ",") <$>
        traverse (prType outer_prec) params
      | otherwise ->
        application (parens (text ("TupleTy " ++ show n))) <$>
        traverse (prType outer_prec) params
    AppTy _ _ -> 
      -- Should not happen after uncurrying
      internalError "prType"
  where
    conName c =
      case tcName c
      of Nothing    -> pprGetTyConName (tcID c)
         Just label -> pure $ text $ showLabel label
    parenthesize expr_prec doc
      | prec > expr_prec = parens doc
      | otherwise = doc
    
    x `arrow` y = (\x_doc y_doc -> x_doc <+> text "->" <+> y_doc) <$> x <*> y
    
    application hd params =
      parenthesize app_prec $ sep (hd : params)

-------------------------------------------------------------------------------
-- Conversion to System F

-- | Get the System F equivalent of a type variable.  It's created if it didn't
-- exist.  The variable must not have been unified with anything.
tyVarToSystemF :: TyCon -> IO SystemF.Var
tyVarToSystemF c
  | not $ isTyVar c = fail "Expecting a variable"
  | otherwise = do -- Check that the variable hasn't been unified
                   when (isFlexibleTyVar c) $ assertCanonicalTyVar c
                   readOrCreateVariable $ tcSystemFVariable c
  where
    readOrCreateVariable ref = do
      x <- readIORef ref
      case x of
        Just v  -> return v
        Nothing -> do
          id <- getNextVarIdent
          let v = mkVar id (tcName c) TypeLevel
          writeIORef ref (Just v)
          return v
      
tyConToSystemF :: TyCon -> IO SystemF.RType
tyConToSystemF c
  | isTyVar c = fail "Expecting a constructor"
  | otherwise = return $ tcSystemFValue $ tcConInfo c

