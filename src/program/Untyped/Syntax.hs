
{-# LANGUAGE DeriveDataTypeable #-}
module Untyped.Syntax where

import Control.Monad
import Data.Maybe
import Data.Typeable(Typeable)
import Debug.Trace

import Common.SourcePos
import Common.Supply
import Common.Identifier
import Common.Label
import Export
import Untyped.Type
import Untyped.Data
import Untyped.Variable
import Type.Var(Var)

data Ann = Ann SourcePos

predefinedVariable :: Maybe Label -> Maybe Var -> IO Variable
predefinedVariable lab trans = do
  id <- getNextVariableID
  return $ Variable id lab trans

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
    -- | A list expression
  | ListE
    { expAnnotation :: Ann
    , expElements :: [Expression]
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
    -- | A function or data constructor call
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
    -- | A static type assertion.
    --   Verify the assertion (during type checking), then continue.
  | TypeAssertE
    { expAnnotation :: Ann
    , expVar :: Variable
    , expType :: HMType
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

-- | Annotations on a function definition
data FunctionAnn = FunctionAnn { funInline :: !Bool}

data FunctionDef = FunctionDef !Variable FunctionAnn Function
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
  getSourcePos (FunctionDef _ _ f) = getSourcePos f

-------------------------------------------------------------------------------

explicitPatternType :: Pattern -> Maybe HMType
explicitPatternType (WildP _) = Nothing

explicitPatternType (VariableP _ _ t) = t

explicitPatternType (TupleP _ fs) =
  tupleTy `liftM` mapM explicitPatternType fs

-- | Is the function definition explicitly annotated with a type? 
explicitlyTyped :: FunctionDef -> Bool
explicitlyTyped (FunctionDef _ _ f) = isJust $ funQVars f

-- | Get the explicitly annotated type information from a function definition.
--   Return 'Nothing' if some annotations are missing.
explicitFunctionType :: FunctionDef -> Maybe (Qualified ([HMType], HMType))
explicitFunctionType (FunctionDef _ _ f) = do
  qvars <- funQVars f
  let cst = trace "FIXME: Must take explicitly annotated constraint from annotation!" []
  param_types <- mapM explicitPatternType $ funParameters f
  return_type <- funReturnType f
  return $ Qualified qvars cst (param_types, return_type)

-- | Get the explicitly annotated type scheme.  Return 'Nothing' if some
--   annotations are missing.
explicitPolyType :: FunctionDef -> Maybe TyScheme
explicitPolyType def =
  fmap (fmap $ uncurry functionTy) $ explicitFunctionType def
