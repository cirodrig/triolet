
{-# LANGUAGE DeriveDataTypeable #-}
module Untyped.Syntax where

import Control.Concurrent.MVar
import Data.Function
import Data.Typeable(Typeable)
import System.IO.Unsafe

import Gluon.Common.SourcePos
import Gluon.Common.Supply
import Gluon.Common.Identifier
import Gluon.Common.Label
import qualified SystemF.Syntax as SystemF
import SystemF.Syntax(Lit(..))
import Untyped.HMType
import Untyped.Data

data Ann = Ann SourcePos

data Variable =
  Variable 
  { varID :: {-# UNPACK #-} !(Ident Variable)
  , varName :: !(Maybe Label)
    -- | If this variable corresponds to a variable in System F, this is the 
    -- System F variable.  Otherwise, this is Nothing.
  , varSystemFVariable :: {-# UNPACK #-} !(Maybe SystemF.Var)
    -- | System F translation of this variable; assigned by type inference
  , varTranslation :: {-# UNPACK #-} !(MVar TypeAssignment)
  }
  deriving(Typeable)

variableIDSupply :: Supply (Ident Variable)
{-# NOINLINE variableIDSupply #-}
variableIDSupply = unsafePerformIO newIdentSupply

getNextVariableID :: IO (Ident Variable)
getNextVariableID = supplyValue variableIDSupply

newVariable :: Maybe Label -> Maybe SystemF.Var -> IO Variable
newVariable lab sf = do
  id <- getNextVariableID
  translation <- newEmptyMVar
  return $ Variable id lab sf translation

predefinedVariable :: Maybe Label -> TypeAssignment -> IO Variable
predefinedVariable lab trans = do
  id <- getNextVariableID
  translation <- newMVar trans
  return $ Variable id lab Nothing translation

instance Eq Variable where
  (==) = (==) `on` varID

instance Ord Variable where
  compare = compare `on` varID

data Pattern =
    WildP
    { patAnnotation :: Ann
    }
  | VariableP
    { patAnnotation :: Ann 
    , patVariable :: Variable 
    , patType :: Maybe HMType
    }
  | TupleP
    { patAnnotation :: Ann
    , patFields :: [Pattern]
    }
  deriving(Typeable)

data Expression =
    -- | A reference to a variable
    VariableE
    { expAnnotation :: Ann
    , expVar :: Variable
    }
    -- | A literal value
  | LiteralE
    { expAnnotation :: Ann
    , expLit :: Lit
    }
    -- | An undefined value
  | UndefinedE
    { expAnnotation :: Ann
    }
    -- | A tuple value
  | TupleE
    { expAnnotation :: Ann
    , expFields :: [Expression]
    }
    -- | A function call
  | CallE
    { expAnnotation :: Ann
    , expOperator :: Expression
    , expOperands :: [Expression]
    }
    -- | An "if" expression
  | IfE
    { expAnnotation :: Ann
    , expCondition :: Expression
    , expIfTrue :: Expression
    , expIfFalse :: Expression
    }
    -- | A lambda expression
  | FunE
    { expAnnotation :: Ann
    , expFunction :: Function
    }
    -- | An assignment expression
  | LetE
    { expAnnotation :: Ann
    , expPattern :: Pattern
    , expArgument :: Expression
    , expBody :: Expression
    }
    -- | A set of function definitions
  | LetrecE
    { expAnnotation :: Ann
    , expDefinitions :: [FunctionDef]
    , expBody :: Expression
    }
  deriving(Typeable)

data Function =
  Function
  { funAnnotation :: Ann
  , funQVars :: Maybe [TyCon]   -- ^ Optional explicitly supplied forall-variables
  , funParameters :: [Pattern]
  , funReturnType :: Maybe HMType
  , funBody :: Expression
  }
  deriving(Typeable)

data FunctionDef = FunctionDef !Variable Function
                 deriving(Typeable)

type DefGroup = [FunctionDef]

data Export = Export
              { exportAnnotation :: Ann 
              , exportVariable :: Variable
              }
              deriving(Typeable)

data Module = Module [DefGroup] [Export]
            deriving(Typeable)

instance HasSourcePos Expression where
  getSourcePos e = case expAnnotation e of Ann pos -> pos
  setSourcePos e p = e {expAnnotation = Ann p}

instance HasSourcePos Function where
  getSourcePos f = case funAnnotation f of Ann pos -> pos
  setSourcePos f p = f {funAnnotation = Ann p}

instance HasSourcePos FunctionDef where
  getSourcePos (FunctionDef _ f) = getSourcePos f
  setSourcePos (FunctionDef v f) p = FunctionDef v (setSourcePos f p)