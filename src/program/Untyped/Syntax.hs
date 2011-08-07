
{-# LANGUAGE DeriveDataTypeable #-}
module Untyped.Syntax where

import Control.Concurrent.MVar
import Data.Function
import Data.Typeable(Typeable)
import System.IO.Unsafe

import Common.SourcePos
import Common.Supply
import Common.Identifier
import Common.Label
import Export
import qualified SystemF.Syntax as SystemF
import Untyped.Data
import Type.Var(Var)

data Ann = Ann SourcePos

data Variable =
  Variable 
  { varID :: {-# UNPACK #-} !(Ident Variable)
  , varName :: !(Maybe Label)
    -- | If this variable corresponds to a variable in System F, this is the 
    -- System F variable.  Otherwise, this is Nothing.
  , varSystemFVariable :: {-# UNPACK #-} !(Maybe Var)
    -- | System F translation of this variable; assigned by type inference
  , varTranslation :: {-# UNPACK #-} !(MVar TypeAssignment)
  }
  deriving(Typeable)

variableIDSupply :: Supply (Ident Variable)
{-# NOINLINE variableIDSupply #-}
variableIDSupply = unsafePerformIO newIdentSupply

getNextVariableID :: IO (Ident Variable)
getNextVariableID = supplyValue variableIDSupply

newVariable :: Maybe Label -> Maybe Var -> IO Variable
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

data Lit = IntL !Integer
         | FloatL !Double
         | BoolL !Bool
         | NoneL

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

data Export =
  Export
  { exportAnnotation :: Ann 
  , exportSpec :: {-# UNPACK #-}!ExportSpec
  , exportVariable :: Variable
  , exportType :: HMType
  }
  deriving(Typeable)

data Module = Module !ModuleName [DefGroup] [Export]
            deriving(Typeable)

instance HasSourcePos Expression where
  getSourcePos e = case expAnnotation e of Ann pos -> pos

instance HasSourcePos Function where
  getSourcePos f = case funAnnotation f of Ann pos -> pos

instance HasSourcePos FunctionDef where
  getSourcePos (FunctionDef _ f) = getSourcePos f
