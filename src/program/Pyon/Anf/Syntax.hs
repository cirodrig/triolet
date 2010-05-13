
{-# LANGUAGE TypeFamilies, DeriveDataTypeable, FlexibleInstances #-}
module Pyon.Anf.Syntax where

import Control.Monad
import Data.Typeable

import Gluon.Common.SourcePos
import Gluon.Core
import Gluon.Core.RenameBase
import Gluon.Core.Level

data family ValOf s :: * -> *
data family StmOf s :: * -> *
data family ProcOf s :: * -> *
     
type RecVal s = ValOf s s
type RVal = RecVal Rec
type Val s = ValOf Rec s

type RecStm s = StmOf s s
type RStm = RecStm Rec
type Stm s = StmOf Rec s

type RecProc s = ProcOf s s
type RProc = RecProc Rec
type Proc s = ProcOf Rec s

type RAlt = Alt Rec
type RModule = Module Rec

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
    , valProc :: RecProc s
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

data instance ProcOf Rec s =
  Proc
  { procInfo :: !SynInfo
  , procParams :: [Binder s ()]
  , procReturnType :: RecExp s
  , procEffectType :: RecExp s
  , procBody :: RecStm s
  }

instance HasSourcePos (ProcOf Rec s) where
  getSourcePos p = getSourcePos (procInfo p)
  setSourcePos p pos = p {procInfo = setSourcePos (procInfo p) pos}

data ProcDef s = ProcDef Var (RecProc s)
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

-------------------------------------------------------------------------------

mapVal :: (Structure a, Structure b) =>
          (RecExp a -> RecExp b)
       -> (RecVal a -> RecVal b)
       -> (RecProc a -> RecProc b)
       -> Val a -> Val b
mapVal exp val proc value =
  case value
  of GluonV info e -> GluonV info (exp e)
     AppV info op args -> AppV info (val op) (map val args)
     LamV info f -> LamV info (proc f)

mapStm :: (Structure a, Structure b) =>
          (RecExp a -> RecExp b)
       -> (RecVal a -> RecVal b)
       -> (RecStm a -> RecStm b)
       -> (RecProc a -> RecProc b)
       -> Stm a -> Stm b
mapStm exp val stm proc statement =
  case statement
  of ReturnS info v -> ReturnS info (val v)
     CallS info v -> CallS info (val v)
     LetS info binder rhs body ->
       LetS info (mapBinder id exp binder) (stm rhs) (stm body)
     LetrecS info defs body ->
       LetrecS info (map map_def defs) (stm body)
     CaseS info scr alts ->
       CaseS info (val scr) (map map_alt alts)
  where
    map_def (ProcDef v p) = ProcDef v (proc p)
    map_alt (Alt con params body) =
      Alt con (map (mapBinder id exp) params) (stm body)

mapProc :: (Structure a, Structure b) =>
           (RecExp a -> RecExp b)
        -> (RecStm a -> RecStm b)
        -> Proc a -> Proc b
mapProc exp stm (Proc inf params rt et body) =
  Proc inf (map (mapBinder id exp) params) (exp rt) (exp et) (stm body)

traverseVal :: (Monad m, Structure a, Structure b) =>
               (RecExp a -> m (RecExp b))
            -> (RecVal a -> m (RecVal b))
            -> (RecProc a -> m (RecProc b))
            -> Val a -> m (Val b)
traverseVal exp val proc value =
  case value
  of GluonV info e -> GluonV info `liftM` exp e
     AppV info op args -> AppV info `liftM` val op `ap` mapM val args
     LamV info f -> LamV info `liftM` proc f

traverseStm :: (Monad m, Structure a, Structure b) =>
               (RecExp a -> m (RecExp b))
            -> (RecVal a -> m (RecVal b))
            -> (RecStm a -> m (RecStm b))
            -> (RecProc a -> m (RecProc b))
            -> Stm a -> m (Stm b)
traverseStm exp val stm proc statement =
  case statement
  of ReturnS info v -> ReturnS info `liftM` val v
     CallS info v -> CallS info `liftM` val v
     LetS info binder rhs body ->
       LetS info `liftM` traverseBinder return exp binder `ap` stm rhs `ap`
       stm body
     LetrecS info defs body ->
       LetrecS info `liftM` mapM map_def defs `ap` stm body
     CaseS info scr alts ->
       CaseS info `liftM` val scr `ap` mapM map_alt alts
  where
    map_def (ProcDef v p) = ProcDef v `liftM` proc p
    map_alt (Alt con params body) =
      Alt con `liftM` mapM (traverseBinder return exp) params `ap` stm body

traverseProc :: (Monad m, Structure a, Structure b) =>
                (RecExp a -> m (RecExp b))
             -> (RecStm a -> m (RecStm b))
             -> Proc a -> m (Proc b)
traverseProc exp stm (Proc inf params rt et body) =
  Proc inf `liftM`
  mapM (traverseBinder return exp) params `ap` exp rt `ap` exp et `ap` stm body