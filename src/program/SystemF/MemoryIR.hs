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
        Pat(MemVarP, MemWildP),
        memVarP, memWildP,
        patMVar,
        patMVar',
        patMType,
        patMUses,
        setPatMUses,
        patMDmd,
        setPatMDmd,
        Ret(..),
        Exp(..),
        Alt(..),
        Fun(..),
        TypM, PatM, TyPatM, RetM, ExpM, AltM, FunM,
        unpackVarAppM, unpackDataConAppM
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

data instance Pat Mem =
    -- | A variable binding.  This binds a value or a pointer, depending on
    --   the representation being used.
    --
    --   * ValPT Nothing: bind a value
    --   * BoxPT, ReadPT, OutPT: bind a pointer
    --   * WritePT: not permitted
    MemVarP
    { _patMBinder :: {-#UNPACK#-}!Binder
    , _patMUses :: {-#UNPACK#-}!Dmd
    }

{-
    -- | A local, dynamically allocated variable.  The dynamically allocated
    --   memory exists as long as the variable is in scope.  The pattern takes
    --   a representation dictionary for this type as a parameter.
    --
    --   This pattern may only appear as the binder of a let expression.
  | LocalVarP 
    { _patMVar :: Var
    , _patMType :: Type
    , _patMDict :: ExpM
    , _patMUses :: {-#UNPACK#-}!Dmd
    } -}
    
    -- | A wildcard pattern.  No variable is bound to this value.
    --
    -- This pattern may only appear in a function parameter or case 
    -- alternative.  It may not appear in a let expression.
  | MemWildP 
    { _patMType :: Type
    }

memVarP :: Binder -> PatM
memVarP binder = MemVarP binder unknownDmd

memWildP :: Type -> PatM
memWildP pt = MemWildP pt

patMVar :: PatM -> Maybe Var
patMVar (MemVarP (v ::: _) _) = Just v
patMVar (MemWildP {}) = Nothing

patMVar' :: PatM -> Var
patMVar' p = case patMVar p of Just v -> v

patMType :: PatM -> Type
patMType (MemVarP {_patMBinder = _ ::: ty}) = ty
patMType (MemWildP {_patMType = ty}) = ty

{-
-- | Get the representation of the value bound to this pattern.
--   It's an error to call this on a 'LocalVarP'.
patMRepr :: PatM -> ParamRepr
patMRepr (MemVarP {_patMParamType = prepr ::: _}) = prepr
patMRepr (LocalVarP {}) = internalError "patMRepr"
patMRepr (MemWildP {_patMParamType = prepr ::: _}) = prepr

-- | Get the representation of the value bound to this pattern.
patMParamType :: PatM -> Type
patMParamType (MemVarP {_patMParamType = pt}) = pt
patMParamType (MemWildP {_patMParamType = pt}) = pt
patMParamType (LocalVarP {}) = internalError "patMParamType"

-- | Get the representation of the value bound by this pattern.
--   For let expressions, this is the representation seen in the body
--   of the expression, not the representation seen in the RHS.
patMReturnRepr :: PatM -> ReturnRepr
patMReturnRepr (MemVarP {_patMParamType = prepr ::: _}) =
  paramReprToReturnRepr prepr
patMReturnRepr (LocalVarP {}) = ReadRT
patMReturnRepr (MemWildP {_patMParamType = prepr ::: _}) =
  paramReprToReturnRepr prepr

patMReturnType :: PatM -> ReturnType
patMReturnType pat = patMReturnRepr pat ::: patMType pat
-}

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
patMDmd (MemVarP {_patMUses = u}) = u
patMDmd (MemWildP {}) = bottom

setPatMDmd :: Dmd -> PatM -> PatM
setPatMDmd m pat = pat {_patMUses = m}

newtype instance TyPat Mem  = TyPatM Binder
newtype instance Ret Mem = RetM {fromRetM :: Type}
newtype instance Exp Mem = ExpM {fromExpM :: BaseExp Mem}
newtype instance Alt Mem = AltM {fromAltM :: BaseAlt Mem}
newtype instance Fun Mem = FunM {fromFunM :: BaseFun Mem}

type TypM = Typ Mem
type PatM = Pat Mem
type TyPatM = TyPat Mem
type RetM = Ret Mem
type ExpM = Exp Mem
type AltM = Alt Mem
type FunM = Fun Mem

unpackVarAppM :: ExpM -> Maybe (Var, [Type], [ExpM])
unpackVarAppM (ExpM (AppE { expOper = ExpM (VarE _ op)
                          , expTyArgs = ts
                          , expArgs = xs})) =
  Just (op, map fromTypM ts, xs)

unpackVarAppM (ExpM (VarE { expVar = op })) =
  Just (op, [], [])

unpackVarAppM _ = Nothing

-- | If the expression is a data constructor application, return the data
--   constructor and arguments
unpackDataConAppM :: TypeEnv -> ExpM -> Maybe (DataConType, [Type], [ExpM])
unpackDataConAppM tenv (ExpM (AppE { expOper = ExpM (VarE _ op)
                                   , expTyArgs = ts
                                   , expArgs = xs}))
  | Just dcon <- lookupDataCon op tenv =
      Just (dcon, map fromTypM ts, xs)

unpackDataConAppM tenv (ExpM (VarE { expVar = op }))
  | Just dcon <- lookupDataCon op tenv =
      Just (dcon, [], [])

unpackDataConAppM _ _ = Nothing
