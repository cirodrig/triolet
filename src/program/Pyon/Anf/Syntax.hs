
{-# LANGUAGE TypeFamilies, DeriveDataTypeable, FlexibleInstances #-}
module Pyon.Anf.Syntax where

import Data.Typeable

import Gluon.Common.SourcePos
import Gluon.Core
import Gluon.Core.Level

data family ValOf s :: * -> *
data family StmOf s :: * -> *
     
type RecVal s = ValOf s s
type RVal = RecVal Rec
type Val s = ValOf Rec s

type RecStm s = StmOf s s
type RStm = RecStm Rec
type Stm s = StmOf Rec s

type RAlt = Alt Rec
type RProc = Proc Rec

-- | Values.  Evaluating a value has no side effects.
data instance ValOf Rec s =
    -- | A Gluon term.  All type expressions are Gluon terms.
    GluonV
    { valInfo :: !SynInfo
    , valGluonTerm :: RecExp s
    }
  | AppV
    { valInfo :: !SynInfo
    , valOper :: RecVal s
    , valArgs :: [RecVal s]
    }
    -- | A lambda function
  | LamV 
    { valInfo :: !SynInfo
    , valProc :: Proc s
    }

instance HasSourcePos (ValOf Rec s) where
  getSourcePos x = getSourcePos (valInfo x)
  setSourcePos x pos = x {valInfo = setSourcePos (valInfo x) pos}

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
    , stmBinder :: Binder s ()
    , stmStm :: RecStm s
    , stmBody :: RecStm s
    }
    -- | Define local functions
  | LetrecS
    { stmInfo :: !SynInfo
    , stmDefs :: ProcDefGroup s
    , stmBody :: RecStm s
    }
    -- | Deconstruct a value
  | CaseS
    { stmInfo :: !SynInfo
    , stmScrutinee :: RecVal s
    , stmAlts :: [Alt s]
    }

instance HasSourcePos (StmOf Rec s) where
  getSourcePos s = getSourcePos (stmInfo s)
  setSourcePos s pos = s {stmInfo = setSourcePos (stmInfo s) pos}

data Proc s =
  Proc
  { procInfo :: !SynInfo
  , procParams :: [Binder s ()]
  , procReturnType :: RecExp s
  , procEffectType :: RecExp s
  , procBody :: RecStm s
  }

data ProcDef s = ProcDef Var (Proc s)
               deriving(Typeable)
type ProcDefGroup s = [ProcDef s]

data Alt s =
  Alt
  { altConstructor :: !Con
  , altParams :: [Binder s ()]  
  , altBody :: RecStm s
  }

data Module s =
  Module [ProcDefGroup s]
  deriving(Typeable)

mkVarV :: SourcePos -> Var -> RVal
mkVarV pos v =
  let info = mkSynInfo pos (getLevel v)
  in GluonV info (VarE info v)

mkInternalVarV :: Var -> RVal
mkInternalVarV v = let e = mkInternalVarE v
                   in GluonV (expInfo e) e

mkConV :: SourcePos -> Con -> RVal
mkConV pos c = 
  let info = mkSynInfo pos (getLevel c)
  in GluonV info (ConE info c)

mkInternalConV :: Con -> RVal
mkInternalConV c = let e = mkInternalConE c
                   in GluonV (expInfo e) e


mkLitV :: SourcePos -> Lit -> RVal
mkLitV pos l =
  let info = mkSynInfo pos (litLevel l)
  in GluonV info (LitE info l)

mkExpV :: RExp -> RVal
mkExpV ty = GluonV (expInfo ty) ty

mkLamV :: Proc Rec -> RVal
mkLamV proc = LamV (procInfo proc) proc

mkAppV :: SourcePos -> RVal -> [RVal] -> RVal
mkAppV pos oper args =
  let info = mkSynInfo pos ObjectLevel
  in AppV info oper args

mkReturnS :: RVal -> RStm
mkReturnS val =
  let info = mkSynInfo (getSourcePos val) ObjectLevel
  in ReturnS info val

mkCallAppS :: SourcePos -> RVal -> [RVal] -> RStm
mkCallAppS pos oper args =
  let info = mkSynInfo pos ObjectLevel
  in CallS info $ AppV info oper args
