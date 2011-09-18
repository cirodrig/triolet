{-| Intermediate representation with explicit data representations. 

This representation extends the pure System F
with more detailed information about how data structures fit
into memory.  Each variable binding gets extra information.
-}

module SystemF.MemoryIR
       (Mem,
        Mentions(..),
        Typ(..),
        TyPat(..),
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
        CInst(..),
        DeCInst(..),
        TypM, PatM, TyPatM, ExpM, AltM, FunM, CInstM, DeCInstM,
        appE, conE,
        unpackVarAppM, unpackDataConAppM, isDataConAppM,
        assumePatM, assumePatMs,
        assumeTyPatM, assumeTyPatMs,
        partitionParameters
       )
where

import Common.Error
import SystemF.Syntax
import SystemF.Demand
import SystemF.DeadCode(Mentions(..))
import Type.Environment
import Type.Type
import Type.Var
import Type.Eval

data Mem

newtype instance Typ Mem = TypM {fromTypM :: Type}

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

newtype instance TyPat Mem  = TyPatM Binder
newtype instance Exp Mem = ExpM {fromExpM :: BaseExp Mem}
newtype instance Alt Mem = AltM {fromAltM :: BaseAlt Mem}
newtype instance Fun Mem = FunM {fromFunM :: BaseFun Mem}
newtype instance CInst Mem = CInstM {fromCInstM :: ConInst}
newtype instance DeCInst Mem = DeCInstM {fromDeCInstM :: DeConInst}

type TypM = Typ Mem
type PatM = Pat Mem
type TyPatM = TyPat Mem
type ExpM = Exp Mem
type AltM = Alt Mem
type FunM = Fun Mem
type CInstM = CInst Mem
type DeCInstM = DeCInst Mem

appE :: ExpInfo -> ExpM -> [TypM] -> [ExpM] -> ExpM
appE _ op [] [] = op
appE inf op type_args args = ExpM (AppE inf op type_args args)

conE :: ExpInfo -> ConInst -> [ExpM] -> ExpM
conE inf op args = ExpM (ConE inf (CInstM op) args)

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
  Just (op, map fromTypM ts, xs)

unpackVarAppM (ExpM (VarE { expVar = op })) =
  Just (op, [], [])

unpackVarAppM _ = Nothing

-- | If the expression is a data constructor (other than a tuple),
--   return the data constructor, type arguments, existential types,
--   and field arguments
unpackDataConAppM :: TypeEnv -> ExpM
                  -> Maybe (DataConType, [Type], [Type], [ExpM])
unpackDataConAppM tenv (ExpM (ConE inf con args)) =
  case fromCInstM con of
    VarCon op ty_args ex_types -> 
      let Just dcon = lookupDataCon op tenv
      in Just (dcon, ty_args, ex_types, args)
    TupleCon types ->
      Nothing

unpackDataConAppM _ _ = Nothing

-- | Return True if the expression is a data constructor or data constructor
--   application.
--
--   The type environment is only used for looking up potential data
--   constructors.
isDataConAppM :: TypeEnv -> ExpM -> Bool
isDataConAppM tenv e = case unpackDataConAppM tenv e
                       of Just _ -> True
                          _ -> False

assumePatM :: TypeEnvMonad m => PatM -> m a -> m a
assumePatM pat m = assumeBinder (patMBinder pat) m

assumePatMs :: TypeEnvMonad m => [PatM] -> m a -> m a
assumePatMs pats m = foldr assumePatM m pats

assumeTyPatM :: TypeEnvMonad m => TyPatM -> m a -> m a
assumeTyPatM (TyPatM b) m = assumeBinder b m

assumeTyPatMs :: TypeEnvMonad m => [TyPatM] -> m a -> m a
assumeTyPatMs pats m = foldr assumeTyPatM m pats

-- | Partition a list of parameters into input and output parameters.
--   Output parameters must follow input parameters.
partitionParameters :: TypeEnv -> [PatM] -> ([PatM], [PatM])
partitionParameters tenv params = go id params 
  where
    -- Take parameters until the first output parameter is found
    go hd (p:ps) =
      case toBaseKind $ typeKind tenv (patMType p)
      of OutK -> (hd [], check_out_kinds (p:ps))
         _    -> go (hd . (p:)) ps

    go hd [] = (hd [], [])
        
    -- Verify that all parameters in the list are output parameters
    check_out_kinds ps
      | and [OutK == toBaseKind (typeKind tenv (patMType p)) | p <- ps] = ps
      | otherwise =
        internalError "partitionParameters: Invalid parameter order"
    
