
module SystemF.Flatten.EffectExp where

data EExp = 
  EExp
  { expInfo :: !SynInfo
  , expReturn :: EReturnType       -- ^ Type of the expression's result value
  , expExp :: !EExp'
  }

data EExp' =
    VarE
    { expVar :: Var
    }
  | ConE 
    { expCon :: !Gluon.Con
    }
  | LitE 
    { expLit :: !Lit 
    , expType :: EType
    }
  | TypeE 
    { expTypeValue :: EType
    }
  | InstE 
    { expPolyOper :: Either Var Con 
    , expPolyArgs :: [Effect]
    }
  | RecPlaceholderE 
    { expVar :: Var 
    , expPlaceholderValue :: !(MVar EExp)
    }
  | CallE
    { expOper :: EExp
    , expArgs :: [EExp]
    }
  | FunE
    { expFun :: EFun
    }
  | DoE
    { expTyArg :: EType
    , expPassConv :: EExp
    , expBody :: EExp
    }
  | LetE
    { expBinder :: EBinder
    , expRhs :: EExp
    , expBody :: EExp
    }
  | LetrecE
    { expDefs :: EDefGroup
    , expBody :: EExp
    }
  | CaseE
    { expScrutinee :: EExp
    , expAlts :: [EAlt]
    }

  -- Coercions
    
  | CoerceValueToBorrowedParam EExp
  | CoerceOwnedToBorrowedParam EExp
  | CoerceValueToBorrowedReturn EExp
  | CoerceOwnedToBorrowedReturn EExp
  | CoerceBorrowedToValue EExp
  | CoerceBorrowedToOwned EExp

data EFun =
  EFun
  { funInfo         :: !SynInfo
  , funEffectParams :: [EVar]
  , funParams       :: [EParam]
  , funReturnType   :: EReturnType
  , funEffect       :: Effect
  , funBody         :: EExp
  }

type Endo a = a -> a

-- | The effect inference monad.  When effect inference runs, it keeps track
-- of constraints and free effect variables in the code that it scans.
newtype EI a =
  EI {runEI :: EffectEnv -> IO (a, Endo Constraint, Endo [EffectVar])}

data EffectEnv =
  EffectEnv
  { -- | Environment used by 'RegionM'
    efRegionEnv :: {-# UNPACK #-}!RegionEnv
    
    -- | Effect types assigned to variables in the environment
  , efEnv :: !(IntMap.IntMap EffectAssignment)
  }

instance Monad EI

addPredicate :: Predicate -> EI ()

addConstraint :: Constraint -> EI ()

extractConstraint :: EI a -> EI (a, Constraint)

newEffectVar :: EI EffectVar



-- | Perform effect inference on an expression.
-- Effect inference returns a new expression with explicit coercions and
-- effect parameters, the inferred return type, and the inferred
-- side effect.
inferExp :: SF.TRExp -> EI (EExp, EReturnType, Effect)