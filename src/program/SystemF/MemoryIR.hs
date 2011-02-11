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
        Pat(MemVarP, LocalVarP, MemWildP),
        memVarP, localVarP, memWildP,
        patMVar,
        patMVar',
        patMType,
        patMParamType,
        patMRepr,
        patMReturnType,
        patMReturnRepr,
        patMDict,
        patMUses,
        setPatMUses,
        Ret(..),
        Exp(..),
        Alt(..),
        Fun(..),
        TypM, PatM, TyPatM, RetM, ExpM, AltM, FunM, unpackVarAppM
       )
where

import Common.Error
import SystemF.Syntax
import SystemF.DeadCode(Mentions(..))
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
    { _patMVar :: Var 
    , _patMParamType :: {-#UNPACK#-}!ParamType
    , _patMUses :: !Mentions
    }

    -- | A local, dynamically allocated variable.  The dynamically allocated
    --   memory exists as long as the variable is in scope.  The pattern takes
    --   a representation dictionary for this type as a parameter.
    --
    --   This pattern may only appear as the binder of a let expression.
  | LocalVarP 
    { _patMVar :: Var
    , _patMType :: Type
    , _patMDict :: ExpM
    , _patMUses :: !Mentions
    }
    
    -- | A wildcard pattern.  No variable is bound to this value.
    --
    -- This pattern may only appear in a function parameter or case 
    -- alternative.  It may not appear in a let expression.
  | MemWildP 
    { _patMParamType :: {-#UNPACK#-}!ParamType
    }

memVarP :: Var -> ParamType -> PatM
memVarP v pt = MemVarP v pt Many

localVarP :: Var -> Type -> ExpM -> PatM
localVarP v t d = LocalVarP v t d Many

memWildP :: ParamType -> PatM
memWildP pt = MemWildP pt

patMVar :: PatM -> Maybe Var
patMVar (MemVarP {_patMVar = v}) = Just v
patMVar (LocalVarP {_patMVar = v}) = Just v
patMVar (MemWildP {}) = Nothing

patMVar' :: PatM -> Var
patMVar' = _patMVar

patMType :: PatM -> Type
patMType (MemVarP {_patMParamType = _ ::: ty}) = ty
patMType (LocalVarP {_patMType = ty}) = ty
patMType (MemWildP {_patMParamType = _ ::: ty}) = ty

patMDict (LocalVarP {_patMDict = d}) = d
patMDict _ = internalError "patMDict"

-- | Get the representation of the value bound to this pattern.
--   It's an error to call this on a 'LocalVarP'.
patMRepr :: PatM -> ParamRepr
patMRepr (MemVarP {_patMParamType = prepr ::: _}) = prepr
patMRepr (LocalVarP {}) = internalError "patMRepr"
patMRepr (MemWildP {_patMParamType = prepr ::: _}) = prepr

-- | Get the representation of the value bound to this pattern.
patMParamType :: PatM -> ParamType
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

patMUses :: PatM -> Mentions
patMUses = _patMUses

setPatMUses :: Mentions -> PatM -> PatM
setPatMUses m pat = pat {_patMUses = m}

data instance TyPat Mem  = TyPatM Var Type
newtype instance Ret Mem = RetM {fromRetM :: ReturnType}
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