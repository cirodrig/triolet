{-| Intermediate representation with explicit data representations. 

This representation extends the pure System F
with more detailed information about how data structures fit
into memory.  Each variable binding gets extra information.
-}

{-# OPTIONS_GHC -no-auto #-}
module SystemF.MemoryIR
       (Mem,
        Mentions(..),
        Pat(PatM),
        patM,
        patMVar,
        patMType,
        patMBinder,
        patMUses,
        setPatMUses,
        patMDmd,
        setPatMDmd,
        isDeadPattern,
        Exp(..),
        Alt(..),
        Fun(..),
        PatM, ExpM, AltM, FunM,
        varE, litE, appE, conE,
        varE', litE', appE', conE',
        unpackVarAppM, unpackDataConAppM, isDataConAppM,
        assumePatM, assumePatMs,
        assumeTyPat, assumeTyPats,
        assumeFDef,
        assumeFDefGroup,
        assumeGDef,
        assumeGDefGroup,
        functionType,
        entityType,
        partitionParameters,
        mapExpTypes,
        mapFunTypes,
        mapModuleTypes
       )
where

import Control.Monad
import Data.Maybe
  
import Common.Error
import SystemF.Syntax
import SystemF.Demand
import SystemF.DeadCode(Mentions(..))
import Type.Environment
import Type.Type
import Type.Var
import Type.Eval

data Mem

-- | A variable binding in a program.
--   Bindings are annotated with demand information.
data instance Pat Mem =
  PatM
  { _patMBinder :: {-#UNPACK#-}!Binder
  , _patMUses :: {-#UNPACK#-}!Dmd
  }

patM :: Binder -> PatM
patM binder = PatM binder unknownDmd

patMVar :: PatM -> Var
patMVar (PatM (v ::: _) _) = v

patMType :: PatM -> Type
patMType (PatM (_ ::: t) _) = t

patMBinder :: PatM -> Binder
patMBinder = _patMBinder

-- | For compatibility with old code, we can convert between mentions and
--   demand types.
mentionToDmd :: Mentions -> Dmd
mentionToDmd One  = Dmd OnceUnsafe Used
mentionToDmd Many = Dmd ManyUnsafe Used

-- | For compatibility with old code, we can convert between mentions and
--   demand types.  The conversion from 'Dmd' to 'Mentions' is lossy.
dmdToMention :: Dmd -> Mentions
dmdToMention dmd = case multiplicity dmd
                   of Dead       -> One
                      OnceSafe   -> One
                      OnceUnsafe -> One
                      _          -> Many

patMUses :: PatM -> Mentions
patMUses = dmdToMention . _patMUses

setPatMUses :: Mentions -> PatM -> PatM
setPatMUses m pat = pat {_patMUses = mentionToDmd m}

patMDmd :: PatM -> Dmd
patMDmd (PatM {_patMUses = u}) = u

setPatMDmd :: Dmd -> PatM -> PatM
setPatMDmd m pat = pat {_patMUses = m}

-- | Return True if the pattern is marked as dead.
isDeadPattern :: PatM -> Bool
isDeadPattern pat = multiplicity (patMDmd pat) == Dead

newtype instance Exp Mem = ExpM {fromExpM :: BaseExp Mem}
newtype instance Alt Mem = AltM {fromAltM :: BaseAlt Mem}
newtype instance Fun Mem = FunM {fromFunM :: BaseFun Mem}

type PatM = Pat Mem
type ExpM = Exp Mem
type AltM = Alt Mem
type FunM = Fun Mem

varE :: ExpInfo -> Var -> ExpM
varE inf v = ExpM (VarE inf v)

litE :: ExpInfo -> Lit -> ExpM
litE inf v = ExpM (LitE inf v)

appE :: ExpInfo -> ExpM -> [Type] -> [ExpM] -> ExpM
appE _ op [] [] = op
appE inf op type_args args = ExpM (AppE inf op type_args args)

conE :: ExpInfo -> ConInst -> [ExpM] -> ExpM
conE inf op args = ExpM (ConE inf op args)

varE' = varE defaultExpInfo
litE' = litE defaultExpInfo
appE' = appE defaultExpInfo
conE' = conE defaultExpInfo

{- Obsolete; 'BaseAlt' is isomorphic to this tuple type now
-- | Construct a case alternative given a 'MonoCon' and the other required 
--   fields
altFromMonoCon :: DeConInst -> [PatM] -> ExpM -> AltM
altFromMonoCon (VarDeCon con ty_args ex_types) fields body =
  let ex_patterns = map TyPatM ex_types
  in AltM $ DeCon con (map TypM ty_args) ex_patterns fields body

altFromMonoCon (TupleDeCon _) fields body =
  AltM $ DeTuple fields body

altToMonoCon :: AltM -> (DeConInst, [PatM], ExpM)
altToMonoCon (AltM (VarDeCon con ty_args ex_types fields body)) =
  (TupleDeCon con (map fromTypM ty_args) [b | TyPatM b <- ex_types], fields, body)

altToMonoCon (AltM (DeTuple fields body)) =
  (MonoTuple (map patMType fields), fields, body)
-}

unpackVarAppM :: ExpM -> Maybe (Var, [Type], [ExpM])
unpackVarAppM (ExpM (AppE { expOper = ExpM (VarE _ op)
                          , expTyArgs = ts
                          , expArgs = xs})) =
  Just (op, ts, xs)

unpackVarAppM (ExpM (VarE { expVar = op })) =
  Just (op, [], [])

unpackVarAppM _ = Nothing

-- | If the expression is a data constructor (other than a tuple),
--   return the data constructor, type arguments, existential types,
--   and field arguments
unpackDataConAppM :: EvalMonad m => ExpM
                  -> m (Maybe (DataConType, [Type], [Type], [ExpM]))
unpackDataConAppM (ExpM (ConE inf con args)) =
  case con of
    VarCon op ty_args ex_types -> do
      Just dcon <- lookupDataCon op
      return $ Just (dcon, ty_args, ex_types, args)
    TupleCon types ->
      return Nothing

unpackDataConAppM _ = return Nothing

-- | Return True if the expression is a data constructor or data constructor
--   application.
--
--   The type environment is only used for looking up potential data
--   constructors.
isDataConAppM :: EvalMonad m => ExpM -> m Bool
isDataConAppM e = liftM isJust $ unpackDataConAppM e

assumePatM :: TypeEnvMonad m => PatM -> m a -> m a
assumePatM pat m = assumeBinder (patMBinder pat) m

assumePatMs :: TypeEnvMonad m => [PatM] -> m a -> m a
assumePatMs pats m = foldr assumePatM m pats

assumeTyPat :: TypeEnvMonad m => TyPat -> m a -> m a
assumeTyPat (TyPat b) m = assumeBinder b m

assumeTyPats :: TypeEnvMonad m => [TyPat] -> m a -> m a
assumeTyPats pats m = foldr assumeTyPat m pats

assumeFDef :: forall m a. TypeEnvMonad m => FDef Mem -> m a -> m a
{-# INLINE assumeFDef #-}
assumeFDef def m = assume (definiendum def) (functionType $ definiens def) m

assumeGDef :: forall m a. TypeEnvMonad m => GDef Mem -> m a -> m a
{-# INLINE assumeGDef #-}
assumeGDef def m =
  let ty =
        case definiens def
        of FunEnt f  -> functionType f
           DataEnt d -> constType d
  in assume (definiendum def) ty m

assumeFDefGroup :: forall m a b. TypeEnvMonad m =>
                  DefGroup (FDef Mem) -> m a -> m b -> m (a, b)
{-# INLINE assumeFDefGroup #-}
assumeFDefGroup g group_m body_m =
  case g
  of NonRec def -> do x <- group_m 
                      y <- assumeFDef def body_m
                      return (x, y)
     Rec defs -> assume_defs defs $ do x <- group_m
                                       y <- body_m
                                       return (x, y)
  where
    assume_defs :: forall a. [FDef Mem] -> m a -> m a
    assume_defs defs m = foldr assumeFDef m defs

assumeGDefGroup :: forall m a b. TypeEnvMonad m =>
                  DefGroup (GDef Mem) -> m a -> m b -> m (a, b)
{-# INLINE assumeGDefGroup #-}
assumeGDefGroup g group_m body_m =
  case g
  of NonRec def -> do x <- group_m 
                      y <- assumeGDef def body_m
                      return (x, y)
     Rec defs -> assume_defs defs $ do x <- group_m
                                       y <- body_m
                                       return (x, y)
  where
    assume_defs :: forall a. [GDef Mem] -> m a -> m a
    assume_defs defs m = foldr assumeGDef m defs

-- | Get the type of a function using its parameter and return types.
functionType :: FunM -> Type 
functionType (FunM (Fun { funTyParams = ty_params
                        , funParams = params
                        , funReturn = ret
                        })) =
  forallType [b | TyPat b <- ty_params] $
  funType (map patMType params) ret

entityType :: Ent Mem -> Type
entityType (FunEnt f) = functionType f
entityType (DataEnt d) = constType d

-- | Partition a list of parameters into input and output parameters.
--   Output parameters must follow input parameters.
partitionParameters :: [PatM] -> UnboxedTypeEvalM ([PatM], [PatM])
partitionParameters params = go id params
  where
    -- Take parameters until the first output parameter is found
    go hd (p:ps) = do
      base_kind <- typeBaseKind $ patMType p
      case base_kind of
        OutK -> do check_out_kinds (p:ps) 
                   return (hd [], p:ps)
        _    -> go (hd . (p:)) ps

    go hd [] = return (hd [], [])
        
    -- Verify that all parameters in the list are output parameters
    check_out_kinds ps = do
      kinds <- mapM (typeBaseKind . patMType) ps
      unless (all (OutK ==) kinds) $
        internalError "partitionParameters: Invalid parameter order"
    
-------------------------------------------------------------------------------

-- | Transform all types and kinds in an expression.
--
--   The expression should not shadow any types or kinds.
mapExpTypes :: (Kind -> Kind) -> (Type -> Type) -> ExpM -> ExpM
mapExpTypes do_kind do_type expression =
  case fromExpM expression
  of VarE {} -> expression
     LitE {} -> expression
     ConE inf con args ->
       ExpM $ ConE inf (do_constructor con) (continues args)
     AppE inf op ty_args args ->
       ExpM $ AppE inf (continue op) (map do_type ty_args) (continues args)
     LamE inf f ->
       ExpM $ LamE inf (mapFunTypes do_kind do_type f)
     LetE inf b rhs body ->
       ExpM $ LetE inf (mapParamTypes do_type b) (continue rhs) (continue body)
     LetfunE inf defs body ->
       ExpM $ LetfunE inf (fmap do_def defs) (continue body)
     CaseE inf scr alts ->
       ExpM $ CaseE inf (continue scr) (map do_alt alts)
     ExceptE inf ty ->
       ExpM $ ExceptE inf (do_type ty)
     CoerceE inf from_t to_t b ->
       ExpM $ CoerceE inf (do_type from_t) (do_type to_t) (continue b)
     ArrayE inf ty es ->
       ExpM $ ArrayE inf (do_type ty) (continues es)
  where
    continue e = mapExpTypes do_kind do_type e
    continues es = map (mapExpTypes do_kind do_type) es

    do_def (Def v ann f) = Def v ann (mapFunTypes do_kind do_type f)

    do_constructor decon =
      case decon
      of VarCon con_var ty_args ex_types ->
           VarCon con_var (map do_type ty_args) (map do_type ex_types)
         TupleCon ty_args ->
           TupleCon (map do_type ty_args)

    do_alt (AltM (Alt decon params body)) =
      AltM $
      Alt (do_decon decon) (map (mapParamTypes do_type) params) (continue body)

    do_decon (VarDeCon v ts bs) =
      VarDeCon v (map do_type ts) [v ::: do_kind k | v ::: k <- bs]

    do_decon (TupleDeCon ts) =
      TupleDeCon (map do_type ts)

mapParamTypes do_type (PatM (v ::: t) u) = PatM (v ::: do_type t) u

-- | Transform all types and kinds in a function.
--
--   The expression should not shadow any types or kinds.
mapFunTypes :: (Kind -> Kind) -> (Type -> Type) -> FunM -> FunM
mapFunTypes do_kind do_type (FunM f) =
  FunM $ f { funTyParams = [TyPat (v ::: do_kind k)
                           | TyPat (v ::: k) <- funTyParams f]
           , funParams = map (mapParamTypes do_type) $ funParams f
           , funReturn = do_type $ funReturn f
           , funBody = mapExpTypes do_kind do_type $ funBody f}

-- | Transform all types and kinds in a module.
--
--   The module should not shadow any types or kinds.
mapModuleTypes :: (Kind -> Kind) -> (Type -> Type) -> Module Mem -> Module Mem
mapModuleTypes do_kind do_type (Module name imps defs exports) =
  Module name (map gdef imps) (fmap (fmap gdef) defs) (map export exports)
  where
    gdef def = mapDefiniens entity def

    entity (FunEnt f) = FunEnt $ mapFunTypes do_kind do_type f
    entity (DataEnt d) = DataEnt $ do_data d

    do_data (Constant inf ty e) =
      Constant inf (do_type ty) (mapExpTypes do_kind do_type e)

    export e = e {exportFunction = mapFunTypes do_kind do_type $ exportFunction e}
