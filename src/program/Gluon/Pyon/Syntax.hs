

{-# LANGUAGE FlexibleContexts, TypeFamilies #-}

module Gluon.Pyon.Syntax
    (CStmt, CAlt, CPat, CProc, CProcDef,

     PyonSyntax(..),

     -- * Statements
     Value(..),
     Stmt(..),
     Alt(..),
     Pat(..),
     ConParamPat(..),
     ProdPat(..),
     Stream(..),
     ProcDef(..),
     Proc(..),
     ProcParameter(..),

     isStmtProc, isProducerProc,

     -- * Traversal
     mapValue, mapStmt, mapStream, mapProc,
     traverseValue, traverseStmt, traverseStream, traverseProc
    )
where

import Gluon.Common.SourcePos
import Gluon.Core.Annotation
import Gluon.Core.Syntax
import Gluon.Core.Variance

type CStmt = Stmt Core
type CAlt = Alt Core
type CPat = Pat Core
type CProc = Proc Core
type CProcDef = ProcDef Core

class Syntax syn => PyonSyntax syn where
    type StmtOf syn :: *
    type StreamOf syn :: *
    type ProcOf syn :: *

instance PyonSyntax Core where
    type StmtOf Core = Stmt Core
    type StreamOf Core = Stream Core
    type ProcOf Core = Proc Core

-- | Patterns
data Pat syn =
    ConP
    { patCon     :: !Con
    , patParams  :: [ConParamPat]
    }
  | TupP
    { patFields  :: ProdPat syn
    }
  | DefaultP

data ConParamPat =
    RigidP | FlexibleP !Var

-- | Expressions with no side effects (other than reading the environment)
data Value syn =
    PureVal
    { valPos :: !SourcePos
    , valValue :: ExpOf syn
    }
  | ProcVal
    { valPos :: !SourcePos
    , valProcedure :: ProcOf syn
    }

instance HasSourcePos (Value syn) where
    getSourcePos = valPos
    setSourcePos v pos = v {valPos = pos}

-- | Statements
data Stmt syn =
    ReturnS
    { cexpInfo       :: !SynInfo
    , cexpValue      :: !(Value syn)
    }
  | CallS
    { cexpInfo       :: !SynInfo
    , cexpCallee     :: !(Value syn)
    , cexpParameters :: ![Value syn]
    }
  | BindS
    { cexpInfo       :: !SynInfo
    , cexpBoundVar   :: !Var
    , cexpAnte       :: StmtOf syn
    , cexpPost       :: StmtOf syn
    }
  | CaseS
    { cexpInfo       :: !SynInfo
    , cexpScrutinee  :: ExpOf syn
    , cexpAlternatives :: ![Alt syn]
    }
  | LetS
    { cexpInfo       :: !SynInfo
    , cexpBoundVar   :: !Var
    , cexpLetValue   :: ExpOf syn
    , cexpBody       :: StmtOf syn
    }
  | LetrecS
    { cexpInfo       :: !SynInfo
    , cexpProcedures :: ![ProcDef syn]
    , cexpScopeVar   :: !Var
    , cexpBody       :: StmtOf syn
    }

instance HasSourcePos (Stmt a) where
    getSourcePos e   = getSourcePos (cexpInfo e)
    setSourcePos e p = e {cexpInfo = setSourcePos (cexpInfo e) p}

instance HasAnn (Stmt syn) where
    getAnn c = getAnn $ cexpInfo c
    setAnn a c = c {cexpInfo = setAnn a (cexpInfo c)}
    clearAnn a c = c {cexpInfo = clearAnn a (cexpInfo c)}

-- Case alternatives
data Alt syn = Alt
    { altInfo    :: !SynInfo
    , altPat     :: !(Pat syn)
    , altBody    :: StmtOf syn
    }

instance HasSourcePos (Alt a) where
    getSourcePos e   = getSourcePos (altInfo e)
    setSourcePos e p = e {altInfo = setSourcePos (altInfo e) p}

-- | Streams
data Stream syn =
    -- | Execute a statement and return a singleton stream containing the
    --   statement's result value.
    DoR
    { sexpInfo       :: !SynInfo
    , sexpStmt       :: StmtOf syn
    }
    -- | Call a stream function.
  | CallR
    { sexpInfo       :: !SynInfo
    , sexpCallee     :: !(Value syn)
    , sexpParameters :: ![Value syn]
    }

-- A tuple pattern.
-- This pattern binds two variables, which have non-overlapping scopes.
-- The variable inside the binder is in scope over all types within the
-- pattern. 
-- The pattern-bound variable is in scope over the body of the case
-- alternative. 
data ProdPat syn =
    ProdP !Var !(Binder' syn ()) (ProdPat syn)
  | UnitP

-- Procedure definitions, which bind a procedure to a name
data ProcDef syn =
    ProcDef
    { procInfo      :: !SynInfo
    , procName      :: !Var 
    , procProcedure :: ProcOf syn
    }

instance HasAnn (ProcDef syn) where
    getAnn p = getAnn $ procInfo p
    setAnn a p = p {procInfo = setAnn a (procInfo p)}
    clearAnn a p = p {procInfo = clearAnn a (procInfo p)}

-- Procedures
data Proc syn =
    Proc
    { procParams   :: [Binder syn ProcParameter]
    , procReturn   :: ExpOf syn
    , procEffect   :: ExpOf syn
    , procBodyStmt :: StmtOf syn
    }
  | Producer
    { procParams     :: [Binder syn ProcParameter]
    , procReturn     :: ExpOf syn
    , procEffect     :: ExpOf syn
    , procBodyStream :: StreamOf syn
    }

isStmtProc (Proc {}) = True
isStmtProc _         = False

isProducerProc (Producer {}) = True
isProducerProc _             = False

data ProcParameter = ProcParameter
    { -- True if this parameter variable is used as a dependent parameter.
      -- It's used as a dependent parameter if mentioned in a later
      -- pararameter, in the effect type, or in the return type.
      pparamIsDependent :: {-# UNPACK #-} !Bool
    , -- Variance of this procedure parameter.
      pparamVariance :: !Variance
    }

-------------------------------------------------------------------------------

mapValue :: (Syntax a, Syntax b) =>
            (ExpOf a -> ExpOf b)
         -> (ProcOf a -> ProcOf b)
         -> Value a -> Value b
mapValue e proc val =
    case val
    of PureVal pos v -> PureVal pos (e v)
       ProcVal pos p -> ProcVal pos (proc p)

traverseValue :: (Monad m, Syntax a, Syntax b) =>
                 (ExpOf a -> m (ExpOf b))
              -> (ProcOf a -> m (ProcOf b))
              -> Value a -> m (Value b)
traverseValue e proc val =
    case val
    of PureVal pos v -> do v' <- e v
                           return $ PureVal pos v'
       ProcVal pos p -> do p' <- proc p
                           return $ ProcVal pos p'

mapStmt :: (Syntax a, Syntax b) =>
             (ExpOf a -> ExpOf b)
          -> (StmtOf a -> StmtOf b)
          -> (ProcOf a -> ProcOf b)
          -> Stmt a -> Stmt b
mapStmt e stmt proc computation =
    case computation
    of ReturnS info val -> ReturnS info (value val)
       CallS info callee params ->
           CallS info (value callee) (map value params)
       BindS info v ante post -> BindS info v (stmt ante) (stmt post)
       CaseS info val alts -> CaseS info (e val) (map fmapAlt alts)
       LetS info v val body -> LetS info v (e val) (stmt body)
       LetrecS info procs v body ->
           LetrecS info (map fmapProcDef procs) v (stmt body)
    where
      value v = mapValue e proc v

      fmapAlt (Alt info pat body) = Alt info (fmapPat pat) (stmt body)

      fmapPat (ConP c params) = ConP c params
      fmapPat (TupP fields) = TupP (fmapFields fields)
      fmapPat DefaultP = DefaultP

      fmapProcDef (ProcDef info nm p) = ProcDef info nm (proc p)

      fmapFields (ProdP v param fs) =
          ProdP v (mapBinder' id e param) $ fmapFields fs
      fmapFields UnitP = UnitP

traverseStmt :: (Monad m, Syntax a, Syntax b) =>
                 (ExpOf a -> m (ExpOf b))
              -> (StmtOf a -> m (StmtOf b))
              -> (ProcOf a -> m (ProcOf b))
              -> Stmt a -> m (Stmt b)
traverseStmt e s proc computation =
    case computation
    of ReturnS info val -> do
         val' <- value val
         return $ ReturnS info val'
       CallS info callee params -> do
         callee' <- value callee
         params' <- mapM value params
         return $ CallS info callee' params'
       BindS info v ante post -> do
         ante' <- s ante
         post' <- s post
         return $ BindS info v ante' post'
       CaseS info val alts -> do
         val' <- e val
         alts' <- mapM traverseAlt alts
         return $ CaseS info val' alts'
       LetS info v val body -> do
         val' <- e val
         body' <- s body
         return $ LetS info v val' body'
       LetrecS info procs v body -> do
         procs' <- mapM traverseProcDef procs
         body' <- s body
         return $ LetrecS info procs' v body'
    where
      value v = traverseValue e proc v

      traverseAlt (Alt info pat body) = do
          pat' <- traversePat pat
          body' <- s body
          return $ Alt info pat' body'

      traversePat (ConP c params) = return $ ConP c params

      traversePat (TupP fields) = do
        fields' <- traverseFields fields
        return (TupP fields')
          where
            traverseFields (ProdP v param ps) = do
              param' <- traverseBinder' return e param
              ps' <- traverseFields ps
              return $ ProdP v param' ps'

            traverseFields UnitP = return UnitP

      traversePat DefaultP = return DefaultP

      traverseProcDef (ProcDef info v p) = do
        p' <- proc p
        return $ ProcDef info v p'

mapStream :: (Syntax a, Syntax b) =>
             (ExpOf a -> ExpOf b)
          -> (StmtOf a -> StmtOf b)
          -> (ProcOf a -> ProcOf b)
          -> Stream a -> Stream b
mapStream e stmt proc stream =
    case stream
    of DoR info val -> DoR info (stmt val)
       CallR info v vs -> CallR info (value v) (map value vs)
    where
      value v = mapValue e proc v 

traverseStream :: (Monad m, Syntax a, Syntax b) =>
                  (ExpOf a -> m (ExpOf b))
               -> (StmtOf a -> m (StmtOf b))
               -> (ProcOf a -> m (ProcOf b))
               -> Stream a -> m (Stream b)
traverseStream e stmt proc stream =
    case stream
    of DoR info val -> do val' <- stmt val
                          return $ DoR info val'
       CallR info v vs -> do v' <- value v
                             vs' <- mapM value vs
                             return $ CallR info v' vs'
    where
      value v = traverseValue e proc v 

mapProc :: (Syntax a, Syntax b) =>
            (ExpOf a -> ExpOf b)
         -> (StmtOf a -> StmtOf b)
         -> Proc a -> Proc b
mapProc e s (Proc params ret eff body) =
    Proc (map mapBinder params) (e ret) (e eff) (s body)
    where
      mapBinder (Binder v ty param) = Binder v (e ty) param

traverseProc :: (Monad m, Syntax a, Syntax b) =>
                (ExpOf a -> m (ExpOf b))
             -> (StmtOf a -> m (StmtOf b))
             -> Proc a -> m (Proc b)
traverseProc e s (Proc params ret eff body) = do
  params' <- mapM traverseBind params
  ret' <- e ret
  eff' <- e eff
  body' <- s body
  return $ Proc params' ret' eff' body'
    where
      traverseBind (Binder v ty param) = do
        ty' <- e ty
        return $ Binder v ty' param

