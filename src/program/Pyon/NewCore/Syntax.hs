
{-# LANGUAGE TypeFamilies, EmptyDataDecls, DeriveDataTypeable, FlexibleInstances #-}
module Pyon.NewCore.Syntax
       (Structure, Rec,
        RVal, RStm, RDef, RType,
        SynInfo,
        Type,
        Con(..), Var, varName, VarID,
        Binder(..), Binder'(..),
        
        Lit(..),
        ValOf(..),
        Val, RecVal, mkVarV, mkConV, mkLitV, mkConAppV,
        valToExp, valToMaybeExp, expToVal,
        StmOf(..),
        Stm, RecStm,
        Alt(..), Pat(..), ConParamPat(..),
        patternVariables,
        Fun(..), ActionFun, StreamFun,
        Def(..), Definiens(..),
        Module(..),
        
        mapBinder, mapBinder',
        mapVal, mapStm, mapDef,
        
        traverseBinder, traverseBinder',
        traverseVal, traverseStm, traverseDef
       )
where

import Control.Monad
import Data.Maybe
import Data.Typeable
  
import Gluon.Common.Error
import Gluon.Common.SourcePos
import qualified Gluon.Core as Gluon
import Gluon.Core(Rec, Structure(..),
                  SynInfo,
                  RecExp,
                  Con(..), Lit(..),
                  Var, varName, VarID,
                  Binder(..), Binder'(..),
                  mapBinder, mapBinder',
                  traverseBinder, traverseBinder')
import Gluon.Core.Level

type RVal = Val Rec
type RStm = Stm Rec
type RDef = Def Rec
type RType = Type Rec

data family ValOf s :: * -> *
data family StmOf s :: * -> *
       
type RecVal s = ValOf s s
type RecStm s = StmOf s s

-- | Pyon uses Gluon as its type system.
type Type s = Gluon.RecExp s

-- | Values.  Evaluating a value has no side effects.
data instance ValOf Rec s =
    -- | A Gluon term.  All type expressions are Gluon terms.
    GluonV
    { valInfo :: !SynInfo
    , valGluonTerm :: Type s
    }
  | AppV
    { valInfo :: !SynInfo
    , valOper :: RecVal s
    , valArgs :: [RecVal s]
    }
    -- | An ordinary lambda function
  | ALamV 
    { valInfo :: !SynInfo
    , valAFun :: ActionFun s
    }
    -- | A stream lambda function
  | SLamV 
    { valInfo :: !SynInfo
    , valSFun :: StreamFun s
    }
    -- | A \"do\" expression, which produces a stream that evaluates its
    -- statement
  | SDoV 
    { valInfo :: !SynInfo
    , valStm :: RecStm s
    }

type Val = ValOf Rec

-- | Statements.
data instance StmOf Rec s =
    -- | Yield a value
    ReturnS 
    { stmInfo :: !SynInfo
    , stmVal :: RecVal s
    }
    -- | Call an ordinary function
  | CallS 
    { stmInfo :: !SynInfo 
    , stmVal :: RecVal s
    }
    -- | Evaluate something and optionally assign its result to a variable
  | LetS 
    { stmInfo :: !SynInfo
    , stmVar :: !(Maybe Var)
    , stmStm :: RecStm s
    , stmBody :: RecStm s
    }
    -- | Define local functions
  | LetrecS 
    { stmInfo :: !SynInfo
    , stmDefs :: [Def s]
    , stmBody :: RecStm s
    }
    -- | Deconstruct a value
  | CaseS 
    { stmInfo :: !SynInfo
    , stmScrutinee :: RecVal s
    , stmAlts :: [Alt s]
    }
            
type Stm = StmOf Rec

mkVarV :: SourcePos -> Var -> Val Rec
mkVarV pos v = GluonV (Gluon.mkSynInfo pos (getLevel v)) $
               Gluon.mkVarE pos v

mkConV :: SourcePos -> Con -> Val Rec
mkConV pos c = GluonV (Gluon.mkSynInfo pos (getLevel $ conInfo c)) $
               Gluon.mkConE pos c

mkLitV :: SourcePos -> Lit -> Val Rec
mkLitV pos l = GluonV (Gluon.mkSynInfo pos (Gluon.litLevel l)) $
               Gluon.mkLitE pos l
              
mkConAppV :: SourcePos -> Con -> [Val Rec] -> Val Rec
mkConAppV pos c args =
  AppV (Gluon.mkSynInfo pos (getLevel $ conInfo c)) (mkConV pos c) args

-- | Convert a value to an expression.  The value must consist of only  
-- 'GluonV' and 'AppV' terms.  If any other terms are encountered,
-- return _|_.
valToExp :: Val Rec -> Gluon.Exp Rec
valToExp (GluonV {valGluonTerm = t}) = t
valToExp (AppV {valInfo = inf, valOper = op, valArgs = args}) =
  Gluon.mkAppE (getSourcePos inf) (valToExp op) (map valToExp args) 
valToExp _ = internalError "valToExp: Cannot convert to a Gluon expression"

-- | Convert a value to an expression.  The value must consist of only  
-- 'GluonV' and 'AppV' terms.  If any other terms are encountered,
-- return Nothing.
valToMaybeExp :: Val Rec -> Maybe (Gluon.Exp Rec)
valToMaybeExp (GluonV {valGluonTerm = t}) = Just t
valToMaybeExp (AppV {valInfo = inf, valOper = op, valArgs = args}) = do
  op' <- valToMaybeExp op
  args' <- mapM valToMaybeExp args
  return $ Gluon.mkAppE (getSourcePos inf) op' args'
valToMaybeExp _ = Nothing

expToVal :: Gluon.Exp Rec -> Val Rec 
expToVal exp = GluonV (Gluon.expInfo exp) exp

instance HasSourcePos (ValOf Rec syn) where
  getSourcePos v = getSourcePos $ valInfo v
  setSourcePos v p = v {valInfo = setSourcePos (valInfo v) p}

instance HasSourcePos (StmOf Rec syn) where
  getSourcePos s = getSourcePos $ stmInfo s
  setSourcePos s p = s {stmInfo = setSourcePos (stmInfo s) p}

-- | A case alternative.
-- The scrutinee is matched to the pattern, which binds local variables; then
-- the body is executed.
data Alt syn =
    Alt
    { altInfo :: !SynInfo
    , altPat :: Pat
    , altBody :: StmOf syn syn
    }
    deriving(Typeable)

-- | A pattern.
data Pat = 
  ConP 
  { patCon :: Con 
  , patParams :: [ConParamPat]
  }
  deriving(Typeable)

-- | A parameter of a constructor pattern.
-- Each parameter corresponds to one parameter of the constructor.
data ConParamPat =
    -- | A rigid parameter.  This parameter's value is a fixed function of
    -- other values in the context.
    RigidP
    -- | A flexible parameter.  This parameter's value is bound to a variable.
    -- Its type can be inferred from the constructor and scrutinee types.
  | FlexibleP !Var

patternVariables :: Pat -> [Var]
patternVariables (ConP con ps) = catMaybes $ map patternVariable ps
  where
    patternVariable (FlexibleP v) = Just v
    patternVariable RigidP = Nothing

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
  deriving(Typeable)

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
  deriving(Typeable)

data Definiens syn =
  ActionFunDef (ActionFun syn) | StreamFunDef (StreamFun syn)
  deriving(Typeable)
                               
data Module syn = Module [Def syn] deriving(Typeable)

mapVal :: (Structure a, Structure b) =>
          (RecVal a -> RecVal b)
       -> (RecStm a -> RecStm b)
       -> (Type a -> Type b)
       -> Val a -> Val b
mapVal val stm typ value =
  case value
  of GluonV info g -> GluonV info (typ g)
     AppV info oper args -> AppV info (val oper) (map val args)
     ALamV info fun -> ALamV info (mapAFun stm typ fun)
     SLamV info fun -> SLamV info (mapSFun val typ fun)
     SDoV info s -> SDoV info (stm s)

traverseVal :: (Monad m, Structure a, Structure b) =>
               (RecVal a -> m (RecVal b))
            -> (RecStm a -> m (RecStm b))
            -> (Type a -> m (Type b))
            -> Val a -> m (Val b)
traverseVal val stm typ value =
  case value
  of GluonV info g -> GluonV info `liftM` typ g
     AppV info oper args -> AppV info `liftM` val oper `ap` mapM val args
     ALamV info fun -> ALamV info `liftM` traverseAFun stm typ fun
     SLamV info fun -> SLamV info `liftM` traverseSFun val typ fun
     SDoV info s -> SDoV info `liftM` stm s

mapStm :: (Structure a, Structure b) =>
          (RecVal a -> RecVal b)
       -> (RecStm a -> RecStm b)
       -> (Type a -> Type b)
       -> Stm a -> Stm b
mapStm val stm typ statement =
  case statement
  of ReturnS info v -> ReturnS info (val v)
     CallS info v -> CallS info (val v)
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

traverseStm :: (Monad m, Structure a, Structure b) =>
               (RecVal a -> m (RecVal b))
            -> (RecStm a -> m (RecStm b))
            -> (Type a -> m (Type b))
            -> Stm a -> m (Stm b)
traverseStm val stm typ statement =
  case statement
  of ReturnS info v -> ReturnS info `liftM` val v
     CallS info v -> CallS info `liftM` val v
     LetS info v rhs body -> LetS info v `liftM` stm rhs `ap` stm body
     LetrecS info defs body ->
       LetrecS info `liftM` mapM (traverseDef val stm typ) defs
                    `ap` stm body
     CaseS info s a -> CaseS info `liftM` val s `ap` mapM traverseAlt a
  where
    traverseAlt alternative =
      case alternative
      of Alt info pat body ->
           let pat' = pat -- Nothing in the pattern requires substitution
           in Alt info pat' `liftM` stm body

mapAFun :: (Structure a, Structure b) =>
           (RecStm a -> RecStm b)
        -> (Type a -> Type b)
        -> ActionFun a -> ActionFun b
mapAFun stm typ (Fun params retType effType body) =
  Fun (map (mapBinder id typ) params) (typ retType) (typ effType) (stm body)

traverseAFun :: (Monad m, Structure a, Structure b) =>
                (RecStm a -> m (RecStm b))
             -> (Type a -> m (Type b))
             -> ActionFun a -> m (ActionFun b)
traverseAFun stm typ (Fun params retType effType body) =
  Fun `liftM` mapM (traverseBinder return typ) params
      `ap` typ retType `ap` typ effType `ap` stm body

mapSFun :: (Structure a, Structure b) =>
           (RecVal a -> RecVal b)
        -> (Type a -> Type b)
        -> StreamFun a -> StreamFun b
mapSFun val typ (Fun params retType effType body) =
  Fun (map (mapBinder id typ) params) (typ retType) (typ effType) (val body)

traverseSFun :: (Monad m, Structure a, Structure b) =>
                (RecVal a -> m (RecVal b))
             -> (Type a -> m (Type b))
             -> StreamFun a -> m (StreamFun b)
traverseSFun val typ (Fun params retType effType body) =
  Fun `liftM` mapM (traverseBinder return typ) params
      `ap` typ retType `ap` typ effType `ap` val body

mapDef :: (Structure a, Structure b) =>
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

traverseDef :: (Monad m, Structure a, Structure b) =>
               (RecVal a -> m (RecVal b))
            -> (RecStm a -> m (RecStm b))
            -> (Type a -> m (Type b))
            -> Def a -> m (Def b)
traverseDef val stm typ (Def info var definition) = do
  definition' <- 
    case definition
    of ActionFunDef afun ->
         ActionFunDef `liftM` traverseAFun stm typ afun
       StreamFunDef sfun ->
         StreamFunDef `liftM` traverseSFun val typ sfun
  return $ Def info var definition'
