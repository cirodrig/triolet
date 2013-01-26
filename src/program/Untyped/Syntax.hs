
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
  , funParameters :: [Pattern]
  , funReturnType :: Maybe HMType
  , funBody :: Expression
  }
  deriving(Typeable)

-- | Annotations on a function definition
data FunctionAnn =
  FunctionAnn
  { -- | A polymorphic type signature specified by user
    funPolySignature :: !PolySignature

    -- | If true, it's highly desirable to inline this function
  , funInline :: !Bool}

-- | A polymorphic type signature, controlling how a function's type is
--   generalized by type inference
data PolySignature =
    -- | Type inference should use this signature, given explicitly by user
    GivenSignature [TyCon] Constraint
    -- | Type inference should infer a polymorphic type signature
  | InferPolymorphicType
    -- | Type inference should infer a type signature, but should not
    --   generalize.
  | InferMonomorphicType

isGivenSignature (GivenSignature _ _) = True
isGivenSignature _ = False

isInferredPolymorphicSignature InferPolymorphicType = True
isInferredPolymorphicSignature _ = False

isInferredMonomorphicSignature InferMonomorphicType = True
isInferredMonomorphicSignature _ = False

data FunctionDef = FunctionDef !Variable FunctionAnn Function
                 deriving(Typeable)

functionDefAnn (FunctionDef _ ann _) = ann

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

-- | Get the explicitly annotated type information from a function definition.
--   Return 'Nothing' if some annotations are missing.
explicitFunctionType :: FunctionDef -> Maybe (Qualified ([HMType], HMType))
explicitFunctionType (FunctionDef _ ann f) = do
  GivenSignature qvars cst <- return (funPolySignature ann)
  param_types <- mapM explicitPatternType $ funParameters f
  return_type <- funReturnType f
  return $ Qualified qvars cst (param_types, return_type)

-- | Get the explicitly annotated type scheme.  Return 'Nothing' if some
--   annotations are missing.
explicitPolyType :: FunctionDef -> Maybe TyScheme
explicitPolyType def =
  fmap (fmap $ uncurry functionTy) $ explicitFunctionType def
