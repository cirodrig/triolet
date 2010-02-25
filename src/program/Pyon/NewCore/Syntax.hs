
{-# LANGUAGE TypeFamilies, EmptyDataDecls #-}
module Pyon.NewCore.Syntax
       (Syntax(..), PyonSyntax(..), Core,
        SynInfo,
        Type,
        Con(..), Var, varName, VarID,
        Binder(..), Binder'(..),
        
        Lit(..),
        Val(..), RecVal,
        Stm(..), RecStm,
        Alt(..), Pat(..), ConParamPat(..),
        Fun(..), ActionFun, StreamFun,
        Def(..), Definiens(..),
        
        mapBinder, mapBinder',
        mapVal, mapStm, mapDef
       )
where

import Gluon.Common.SourcePos
import qualified Gluon.Core as Gluon
import Gluon.Core(Core, Syntax(..),
                  SynInfo,
                  RecExp,
                  Con(..), Var, varName, VarID,
                  Binder(..), Binder'(..),
                  mapBinder, mapBinder',
                  traverseBinder, traverseBinder')
import Gluon.Core.Rename(SubstitutingT)

class Syntax syn => PyonSyntax syn where
  type ValOf syn :: * -> *
  type StmOf syn :: * -> *
       
instance PyonSyntax Core where
  type ValOf Core = Val
  type StmOf Core = Stm

type RecVal syn = ValOf syn syn
type RecStm syn = StmOf syn syn

-- | Pyon uses Gluon as its type system.
type Type syn = Gluon.RecExp syn

-- | A literal value.
data Lit = IntL {-# UNPACK #-} !Integer 
         | FloatL {-# UNPACK #-} !Double

-- | Values.  Evaluating a value has no side effects.
data Val syn =
    -- | A Gluon term.  All type expressions are Gluon terms.
    GluonV
    { valInfo :: !SynInfo
    , valGluonTerm :: Type syn
    }
    -- | An object-level variable reference.
  | VarV
    { valInfo :: !SynInfo
    , valVar :: Var
    }
  | LitV
    { valInfo :: !SynInfo
    , valLit :: Lit
    }
  | ConV
    { valInfo :: !SynInfo
    , valCon :: Con
    }
  | AppV
    { valInfo :: !SynInfo
    , valOper :: RecVal syn
    , valArgs :: [RecVal syn]
    }
    -- | An ordinary lambda function
  | ALamV 
    { valInfo :: !SynInfo
    , valAFun :: ActionFun syn
    }
    -- | A stream lambda function
  | SLamV 
    { valInfo :: !SynInfo
    , valSFun :: StreamFun syn
    }
    -- | A \"do\" expression, which produces a stream that evaluates its
    -- statement
  | SDoV 
    { valInfo :: !SynInfo
    , valStm :: RecStm syn
    }

-- | Statements.
data Stm syn =
    -- | Yield a value
    ReturnS 
    { stmInfo :: !SynInfo
    , stmVal :: RecVal syn
    }
    -- | Call an ordinary function
  | CallS 
    { stmInfo :: !SynInfo 
    , stmOper :: RecVal syn
    , stmArgs :: [RecVal syn]
    }
    -- | Evaluate something and optionally assign its result to a variable
  | LetS 
    { stmInfo :: !SynInfo
    , stmVar :: !(Maybe Var)
    , stmStm :: RecStm syn
    , stmBody :: RecStm syn
    }
    -- | Define local functions
  | LetrecS 
    { stmInfo :: !SynInfo
    , stmDefs :: [Def syn]
    , stmBody :: RecStm syn
    }
    -- | Deconstruct a value
  | CaseS 
    { stmInfo :: !SynInfo
    , stmScrutinee :: RecVal syn
    , stmAlts :: [Alt syn]
    }

instance HasSourcePos (Val syn) where
  getSourcePos v = getSourcePos $ valInfo v
  setSourcePos v p = v {valInfo = setSourcePos (valInfo v) p}

-- | A case alternative.
-- The scrutinee is matched to the pattern, which binds local variables; then
-- the body is executed.
data Alt syn =
    Alt
    { altInfo :: !SynInfo
    , altPat :: Pat
    , altBody :: StmOf syn syn
    }

-- | A pattern.
data Pat = 
  ConP 
  { patCon :: Con 
  , patParams :: [ConParamPat]
  }

-- | A parameter of a constructor pattern.
-- Each parameter corresponds to one parameter of the constructor.
data ConParamPat =
    -- | A rigid parameter.  This parameter's value is a fixed function of
    -- other values in the context.
    RigidP
    -- | A flexible parameter.  This parameter's value is bound to a variable.
    -- Its type can be inferred from the constructor and scrutinee types.
  | FlexibleP !Var

-- | A function definition.
--
-- For stream functions, 'funEffectType' is ignored.
data Fun syn body =
  Fun
  { funParams :: [Binder syn ()]
  , funReturnType :: Type syn
  , funEffectType :: Type syn
  , funBody :: body
  }

-- | An ordinary function.
type ActionFun syn = Fun syn (RecStm syn)

-- | A stream function.
type StreamFun syn = Fun syn (RecVal syn)

-- | A definition.
data Def syn =
  Def
  { defInfo :: !SynInfo
  , definiendum :: Var
  , definiens :: Definiens syn
  }

data Definiens syn =
  ActionFunDef (ActionFun syn) | StreamFunDef (StreamFun syn)
                               
mapVal :: (PyonSyntax a, PyonSyntax b) =>
          (RecVal a -> RecVal b)
       -> (RecStm a -> RecStm b)
       -> (Type a -> Type b)
       -> Val a -> Val b
mapVal val stm typ value =
  case value
  of GluonV info g -> GluonV info (typ g)
     VarV info v -> VarV info v
     LitV info l -> LitV info l 
     ConV info c -> ConV info c 
     AppV info oper args -> AppV info (val oper) (map val args)
     ALamV info fun -> ALamV info (mapAFun stm typ fun)
     SLamV info fun -> SLamV info (mapSFun val typ fun)
     SDoV info s -> SDoV info (stm s)

mapStm :: (PyonSyntax a, PyonSyntax b) =>
          (RecVal a -> RecVal b)
       -> (RecStm a -> RecStm b)
       -> (Type a -> Type b)
       -> Stm a -> Stm b
mapStm val stm typ statement =
  case statement
  of ReturnS info v -> ReturnS info (val v)
     CallS info oper args -> CallS info (val oper) (map val args)
     LetS info v rhs body -> LetS info v (stm rhs) (stm body)
     LetrecS info defs body ->
       LetrecS info (map (mapDef val stm typ) defs) (stm body)
     CaseS info s a -> CaseS info (val s) (map mapAlt a)
  where
    mapAlt alternative =
      case alternative
      of Alt info pat body ->
           let pat' = pat -- Nothing in the pattern requires substitution
           in Alt info pat' (stm body)

mapAFun :: (PyonSyntax a, PyonSyntax b) =>
           (RecStm a -> RecStm b)
        -> (Type a -> Type b)
        -> ActionFun a -> ActionFun b
mapAFun stm typ (Fun params retType effType body) =
  Fun (map (mapBinder id typ) params) (typ retType) (typ effType) (stm body)

mapSFun :: (PyonSyntax a, PyonSyntax b) =>
           (RecVal a -> RecVal b)
        -> (Type a -> Type b)
        -> StreamFun a -> StreamFun b
mapSFun val typ (Fun params retType effType body) =
  Fun (map (mapBinder id typ) params) (typ retType) (typ effType) (val body)

mapDef :: (PyonSyntax a, PyonSyntax b) =>
          (RecVal a -> RecVal b)
       -> (RecStm a -> RecStm b)
       -> (Type a -> Type b)
       -> Def a -> Def b
mapDef val stm typ (Def info var definition) =
  let definition' = case definition
                    of ActionFunDef afun ->
                         ActionFunDef $ mapAFun stm typ afun
                       StreamFunDef sfun ->
                         StreamFunDef $ mapSFun val typ sfun
  in Def info var definition'