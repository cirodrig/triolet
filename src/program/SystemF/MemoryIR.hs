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
        TypM, PatM, TyPatM, ExpM, AltM, FunM,
        appE,
        altFromMonoCon, altToMonoCon,
        unpackVarAppM, unpackDataConAppM, isDataConAppM
       )
where

import Common.Error
import SystemF.Syntax
import SystemF.Demand
import SystemF.DeadCode(Mentions(..))
import Type.Environment
import Type.Type
import Type.Var

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

type TypM = Typ Mem
type PatM = Pat Mem
type TyPatM = TyPat Mem
type ExpM = Exp Mem
type AltM = Alt Mem
type FunM = Fun Mem

appE :: ExpInfo -> ExpM -> [TypM] -> [ExpM] -> ExpM
appE _ op [] [] = op
appE inf op type_args args = ExpM (AppE inf op type_args args)

-- | Construct a case alternative given a 'MonoCon' and the other required 
--   fields
altFromMonoCon :: MonoCon -> [PatM] -> ExpM -> AltM
altFromMonoCon (MonoCon con ty_args ex_types) fields body =
  let ex_patterns = map TyPatM ex_types
  in AltM $ DeCon con (map TypM ty_args) ex_patterns fields body

altFromMonoCon (MonoTuple _) fields body =
  AltM $ DeTuple fields body

altToMonoCon :: AltM -> (MonoCon, [PatM], ExpM)
altToMonoCon (AltM (DeCon con ty_args ex_types fields body)) =
  (MonoCon con (map fromTypM ty_args) [b | TyPatM b <- ex_types], fields, body)

altToMonoCon (AltM (DeTuple fields body)) =
  (MonoTuple (map patMType fields), fields, body)

unpackVarAppM :: ExpM -> Maybe (Var, [Type], [ExpM])
unpackVarAppM (ExpM (AppE { expOper = ExpM (VarE _ op)
                          , expTyArgs = ts
                          , expArgs = xs})) =
  Just (op, map fromTypM ts, xs)

unpackVarAppM (ExpM (VarE { expVar = op })) =
  Just (op, [], [])

unpackVarAppM _ = Nothing

-- | If the expression is a data constructor application, return the data
--   constructor, type arguments, existential types, and field arguments
unpackDataConAppM :: TypeEnv -> ExpM
                  -> Maybe (DataConType, [Type], [Type], [ExpM])
unpackDataConAppM tenv (ExpM (AppE { expOper = ExpM (VarE _ op)
                                   , expTyArgs = ts
                                   , expArgs = xs}))
  | Just dcon <- lookupDataCon op tenv =
      let num_tyargs = length (dataConPatternParams dcon)
          types = map fromTypM ts
          ty_args = take num_tyargs types
          ex_types = drop num_tyargs types
      in Just (dcon, ty_args, ex_types, xs)

unpackDataConAppM tenv (ExpM (VarE { expVar = op }))
  | Just dcon <- lookupDataCon op tenv =
      Just (dcon, [], [], [])

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

