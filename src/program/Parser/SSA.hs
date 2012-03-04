
{-# LANGUAGE DoRec #-}
module Parser.SSA
       (JoinNode(..),
        FallthroughCount(..),
        Phi(..), Phis,
        SSAVersion(..),
        setVersion,
        predefinedSSAVar,
        SSAID,
        SSAVar,
        SSAParameter,
        SSAExpr,
        SSAIterFor,
        SSAIterIf,
        SSAIterLet,
        SSAComprehension,
        SSAStmt,
        computeSSA
       )
where

import Prelude hiding(mapM, sequence)

import Control.Applicative
import Control.Monad hiding(mapM, sequence)
import Control.Monad.Fix
import Control.Monad.Trans
import Data.IORef
import qualified Data.Map as Map
import Data.Maybe
import Data.Traversable
import Foreign.Ptr(nullPtr)

import Common.SourcePos
import Parser.ParserSyntax
import Untyped.Data(ParserVarBinding)

-- | A SSA variable version
data SSAVersion =
    NotSSA                      -- ^ Not tracked by SSA
  | SSAUndef                    -- ^ Use of an undefined value
  | SSAVer {-# UNPACK #-}!Int   -- ^ An SSA version
    deriving(Eq, Ord) 

type SSAID = (Int, SSAVersion)

type SSAVar = Var SSAID
type SSAParameter = Parameter SSAID
type SSAExpr = Expr SSAID
type SSAIterFor = IterFor SSAID
type SSAIterIf = IterIf SSAID
type SSAIterLet = IterLet SSAID
type SSAComprehension = Comprehension SSAID
type SSAStmt = Stmt SSAID

setVersion :: PVar -> SSAVersion -> SSAVar
setVersion (Var nm id p) ver = Var nm (id, ver) p

type StmtID = Int

-- | A flag indicating whether a statement may exit via a \'return\' statement
type HasReturn = Bool

-- | The number of fall-through paths out of a control flow statement.
-- Used for converting if-statements.
data FallthroughCount = FTZero | FTOne | FTMany
                      deriving(Eq)

-- | Saturating addition
(#+) :: FallthroughCount -> FallthroughCount -> FallthroughCount
FTZero #+ x      = x
FTOne  #+ FTZero = FTOne
_      #+ _      = FTMany

-- | A phi statement.  The statement defines a new variable version from
-- a set of live-in variable versions.
data Phi = Phi SSAVersion [(StmtID, SSAVersion)]

type Phis = Map.Map PVar Phi

-- | A control flow join point
data JoinNode =
    IfJoin
    { -- | Are there return statements inside this if statement?
      joinReturn      :: !HasReturn
      -- | How many fallthrough paths lead out of this if statement?
    , joinFallthrough :: !FallthroughCount
    , joinPhis        :: Phis
    }
  | ReturnJoin
    { joinPhi         :: Phi
    }

-------------------------------------------------------------------------------
-- SSA computation

-- | A set of live SSA definitions at one scope
type SSAScope = Map.Map PVar SSAVersion

-- | All live definitions at a program point constitute a stack
type SSADefs = [SSAScope]

-- | Information about nonlocal control flow transfers out of statements.
-- Only return statements are supported.
data NonlocalControl =
  NonlocalControl [StmtID] [IORef (Maybe JoinNode)]

emptyNLC = NonlocalControl [] []

newtype SSA a = SSA {runSSA :: SSACtx
                            -> SSADefs
                            -> NonlocalControl -- Writer-like
                            -> IO (a, SSADefs, NonlocalControl)}

instance Functor SSA where
  fmap f (SSA g) = SSA $ \ctx defs w -> do
    (x, defs', w') <- g ctx defs w
    return (f x, defs', w')

instance Applicative SSA where
  pure = return
  m <*> n = m >>= flip fmap n

instance Monad SSA where
  return x = SSA $ \_ defs w -> return (x, defs, w)
  SSA m >>= k = SSA $ \ctx defs w -> do
    (x, defs', w') <- m ctx defs w
    runSSA (k x) ctx defs' w'

instance MonadFix SSA where
  mfix f = SSA $ \ctx defs w ->
    mfix $ \ ~(x, defs', w') -> runSSA (f x) ctx defs w

instance MonadIO SSA where
  liftIO m = SSA $ \_ defs w -> do x <- m
                                   return (x, defs, w)

data SSACtx =
  SSACtx
  { nextVarID :: {-# UNPACK #-} !(IORef Int)
  , nextSSAID :: {-# UNPACK #-} !(IORef Int)
  , nextStmID :: {-# UNPACK #-} !(IORef Int)
  }

newSSAID :: SSA SSAVersion
newSSAID = SSA $ \ctx defs w -> do
  var_id <- readIORef $ nextSSAID ctx
  writeIORef (nextSSAID ctx) $ var_id + 1
  return (SSAVer var_id, defs, w)

newVarID :: SSA Int
newVarID = SSA $ \ctx defs w -> do
  var_id <- readIORef $ nextVarID ctx
  writeIORef (nextVarID ctx) $ var_id + 1
  return (var_id, defs, w)

-- | Create a new SSA variable, using the fields from the parser variable
newSSAVar :: PVar -> SSA SSAVar
newSSAVar v = fmap (setVersion v) newSSAID

newAnonymousSSAVar :: SSA SSAVar
newAnonymousSSAVar = do
  id <- newVarID
  ssa <- newSSAID
  return $ Var "" (id, ssa) nullPtr

predefinedSSAVar :: PVar -> SSAVar
predefinedSSAVar v = Var (varName v) (varID v, NotSSA) nullPtr

newStmtID :: SSA Int
newStmtID = SSA $ \ctx defs w -> do
  id <- readIORef $ nextStmID ctx
  writeIORef (nextStmID ctx) $ id + 1
  return (id, defs, w)

-- | Intercept all nonlocal control flow information 
interceptNonlocalControl :: SSA a -> SSA (NonlocalControl, a)
interceptNonlocalControl m = SSA $ \ctx defs w -> do
  (x, defs, local_w) <- runSSA m ctx defs emptyNLC
  return ((local_w, x), defs, w)

-- | Modify the definitions on the top of the definitions stack
modifyDefs :: (SSADefs -> SSADefs) -> SSA ()
modifyDefs f = SSA $ \_ scopes w -> return ((), f scopes, w)

getDefs :: SSA SSADefs
getDefs = SSA $ \_ scopes w -> return (scopes, scopes, w)

modifyLocalScope :: (SSAScope -> SSAScope) -> SSA ()
modifyLocalScope f = SSA $ \_ (scope:scopes) w ->
  return ((), f scope : scopes, w)

-- | Run a computation in a temporary definition scope
enterScope :: SSA a -> SSA (a, SSAScope)
enterScope m = SSA $ \env scopes w -> do
  (x, scope:scopes', w') <- runSSA m env (Map.empty:scopes) w
  return ((x, scope), scopes', w')

-- | Map the variable to an instance with a new SSA version.
-- Return the new variable.
define :: PVar -> SSA SSAVersion
define v = do
  id <- newSSAID
  modifyLocalScope $ Map.insert v id
  return id

defineV :: PVar -> SSA SSAVar
defineV v = fmap (setVersion v) (define v)

-- | Delete a mapping for a variable.  The variable must not be referenced
-- following the kill.
kill :: PVar -> SSA ()
kill v = modifyLocalScope $ Map.delete v

-- | Get the current SSA version of the variable
use :: PVar -> SSA SSAVersion
use v = return . find_def =<< getDefs
  where
    find_def (defs:defss) = fromMaybe (find_def defss) $ Map.lookup v defs 
    find_def [] = SSAUndef

useV :: PVar -> SSA SSAVar
useV v = fmap (setVersion v) (use v)

type IfBranchInfo = (StmtID, HasReturn, FallthroughCount, [IORef (Maybe JoinNode)])

-- | Perform SSA on the two branches of an 'if' statement
ifControl :: SSA (IfBranchInfo, a)
          -> SSA (IfBranchInfo, a)
          -> SSA (a, a, JoinNode)
ifControl true_path false_path = do
  (((t_id, t_ret, t_ft, t_jref), t_stmt), t_defs) <- enterScope true_path
  (((f_id, f_ret, f_ft, f_jref), f_stmt), f_defs) <- enterScope false_path
  phis <- createPhis [(t_id, t_defs), (f_id, f_defs)]
  
  -- Construct the join node
  let join = IfJoin { joinReturn = t_ret || f_ret
                    , joinFallthrough = t_ft #+ f_ft
                    , joinPhis = phis 
                    }
             
  -- Save the join node
  liftIO $ forM_ (t_jref ++ f_jref) $ \jref -> writeIORef jref (Just join)
  return (t_stmt, f_stmt, join)

-- | Create phi nodes from an 
createPhis :: [(StmtID, SSAScope)] -> SSA Phis
createPhis scopes = do
  -- Generate phi nodes for variables defined in any scope
  let phi_map = Map.unionsWith (++) [Map.map (\n -> [(i, n)]) s
                                    | (i, s) <- scopes]
  phi_list <- mapM make_phi $ Map.toList phi_map
  return $ Map.fromList phi_list
  where
    paths = map fst scopes

    make_phi (pvar, scopes) = do
      phi <- createPhi paths pvar scopes
      return (pvar, phi)
    
createPhi :: [StmtID] -> PVar -> [(StmtID, SSAVersion)] -> SSA Phi
createPhi paths pvar scopes = do
  old_ver <- use pvar
  new_ver <- define pvar

  -- If a variable is not defined on a path, use the original value as
  -- the source
  return $ Phi new_ver [(i, fromMaybe old_ver $ lookup i scopes) | i <- paths]

-------------------------------------------------------------------------------

defineParam :: PParameter -> SSA SSAParameter
defineParam param =
  case param
  of Parameter v ann -> do
       ann' <- traverse ssaExpr ann
       v' <- defineV v
       return $ Parameter v' ann'
     TupleParam ps -> TupleParam <$> traverse defineParam ps

ssaExpr :: PExpr -> SSA SSAExpr
ssaExpr expression =
  case expression
  of Variable pos v    -> Variable pos <$> useV v
     Literal pos l     -> pure $ Literal pos l
     Tuple pos es      -> Tuple pos <$> traverse ssaExpr es 
     Unary pos op x    -> Unary pos op <$> ssaExpr x
     Binary pos op x y -> Binary pos op <$> ssaExpr x <*> ssaExpr y
     Subscript pos x y -> Subscript pos <$> ssaExpr x <*> traverse ssaExpr y
     Slicing pos e ss  -> Slicing pos <$> ssaExpr e <*> traverse ssaSlice ss
     ListComp pos it   -> ListComp pos <$> ssaIterFor it
     Generator pos it  -> Generator pos <$> ssaIterFor it
     Call pos op args  -> Call pos <$> ssaExpr op <*> traverse ssaExpr args
     Cond pos c x y    -> Cond pos <$> ssaExpr c <*> ssaExpr x <*> ssaExpr y
     Let pos b x y     -> do x' <- ssaExpr x
                             b' <- defineParam b
                             y' <- ssaExpr y
                             return $ Let pos b' x' y'
     Lambda pos ps e   -> lambda pos ps e
  where
    lambda pos ps body =
      fmap fst $ enterScope $
      Lambda pos <$> traverse defineParam ps <*> ssaExpr body

ssaSlice :: Slice Int -> SSA (Slice SSAID)
ssaSlice (SliceSlice pos l u ms) =
  SliceSlice pos <$> traverse ssaExpr l <*> traverse ssaExpr u <*>
  traverse (traverse ssaExpr) ms

ssaSlice (ExprSlice e) =
  ExprSlice <$> ssaExpr e

ssaIterFor :: PIterFor Expr -> SSA (SSAIterFor Expr)
ssaIterFor (IterFor pos params dom body) = do
  dom' <- ssaExpr dom
  IterFor pos <$> traverse defineParam params <*> pure dom' <*> ssaComp body

ssaIterIf :: PIterIf Expr -> SSA (SSAIterIf Expr)
ssaIterIf (IterIf pos cond body) =
  IterIf pos <$> ssaExpr cond <*> ssaComp body

ssaIterLet :: PIterLet Expr -> SSA (SSAIterLet Expr)
ssaIterLet (IterLet pos tgt rhs body) = do
  rhs' <- ssaExpr rhs
  IterLet pos <$> defineParam tgt <*> pure rhs' <*> ssaComp body

ssaComp :: PComprehension Expr -> SSA (SSAComprehension Expr)
ssaComp (CompFor it) = CompFor <$> ssaIterFor it
ssaComp (CompIf it)  = CompIf <$> ssaIterIf it
ssaComp (CompLet it) = CompLet <$> ssaIterLet it
ssaComp (CompBody e) = CompBody <$> ssaExpr e

-- | Restructure a statement list into a list of non-control-flow statements 
-- followed by a single control flow transfer.  If there isn't a control flow
-- transfer in the list, create a fallthrough.
regularizeControl :: Bool -> [PStmt] -> SSA ([PStmt], PStmt)
regularizeControl is_function stmts = find_control id stmts
  where
    is_control (Return {}) = True
    is_control (FallThrough {}) = True
    is_control _ = False

    find_control hd (s:ss) | is_control s = return (hd [], s)
                           | otherwise = find_control (hd . (s:)) ss
    find_control hd [] = do
      -- Create a fallthrough statement; or a return None if this is a
      -- function body
      ft_id <- newStmtID
      succ <- liftIO $ newIORef Nothing
      if is_function
        then return (hd [], Return noSourcePos ft_id succ $
                            Literal noSourcePos NoneLit)
        else return (hd [], FallThrough noSourcePos ft_id succ)

-- | Perform SSA on a suite of statements.
ssaSuite :: [PStmt] -> SSA (IfBranchInfo, [SSAStmt])
ssaSuite suite = do
  (stmts, ctl) <- regularizeControl False suite
  ssa_suite stmts ctl
  where
    ssa_suite (stm:stms) ctl = do
      rec { 
      (hasret1, stm') <- ssaStmt (head stms') stm
      ; ((retid, hasret2, hasft, joinrefs), stms') <- ssa_suite stms ctl }
      return ((retid, hasret1 || hasret2, hasft, joinrefs), stm':stms')

    ssa_suite [] ctl = do
      (inf, stm) <- ssaControlStmt ctl
      return (inf, [stm])

-- | Perform SSA evaluation on a control flow statement.
ssaControlStmt :: PStmt -> SSA (IfBranchInfo, SSAStmt)
ssaControlStmt stm =
  case stm
  of Return pos stm_id jp rhs -> do
       rhs' <- ssaExpr rhs
       return ((stm_id, True, FTZero, [jp]), Return pos stm_id jp rhs')

     FallThrough pos stm_id jp ->
       return ((stm_id, False, FTOne, [jp]), FallThrough pos stm_id jp)

     _ -> error "ssaControlStmt"

-- | Perform SSA evaluation on a non-control-flow statement.
ssaStmt :: SSAStmt              -- ^ Next statement (lazy)
        -> PStmt                -- ^ Statment to transform
        -> SSA (HasReturn, SSAStmt)
ssaStmt next_stmt statement =
  case statement
  of ExprStmt pos x -> do x' <- ssaExpr x
                          fall_through $ ExprStmt pos x'
     Assign pos lhs rhs -> do
       rhs' <- ssaExpr rhs
       lhs' <- defineParam lhs
       fall_through $ Assign pos lhs' rhs'
     Assert pos es -> do
       es' <- mapM ssaExpr es
       fall_through $ Assert pos es'
     Require pos x e -> do
       x' <- useV x
       e' <- ssaExpr e
       fall_through $ Require pos x' e'
     If pos c t f _ -> do
       c' <- ssaExpr c
       (true_suite, false_suite, join) <- ifControl (ssaSuite t) (ssaSuite f)
       return (joinReturn join, If pos c' true_suite false_suite (Just join))
     DefGroup pos defs -> do
       defs' <- ssaDefGroup defs 
       fall_through $ DefGroup pos defs'
     _ -> error "ssaStmt"
  where
    fall_through x = return (False, x)
    
ssaDefGroup defs = do 
  -- Define all functions
  vars <- mapM (defineV . funcName) defs
  
  -- Perform SSA on the function bodies
  zipWithM ssa_fun vars defs
  where
    ssa_fun v (Func pos _ ann params ret_ann body _) = do
      ann' <- traverse (traverse ssa_forall_ann) ann
      params' <- mapM defineParam params
      ret_ann' <- traverse ssaExpr ret_ann
      
      -- We only care about return statements out of the body
      (body', return_stm) <- regularizeControl True body
      (return_control, (_, body')) <-
        interceptNonlocalControl $ ssaSuite (body' ++ [return_stm])
      
      -- Create a join node for the function return.
      -- Create new variables for the input return variable along each path.
      let NonlocalControl return_stmts return_refs = return_control
          return_var = makeVar "return" 0
      return_id  <- newSSAID
      return_ids <- replicateM (length return_stmts) newSSAID
      let return_phi = Phi return_id (zip return_stmts return_ids)
          join = ReturnJoin return_phi
      
      return $ Func pos v ann' params' ret_ann' body' (Just join)

    ssa_forall_ann (v, ty) = do
      ty' <- traverse ssaExpr ty
      v' <- defineV v
      return (v', ty')

ssaExport :: ExportItem Int -> SSA (ExportItem SSAID)
ssaExport (ExportItem { exportPos = pos 
                      , exportSpec = spec
                      , exportVar = v
                      , exportType = ty}) = do
  v' <- useV v
  ty' <- ssaExpr ty
  return $ ExportItem pos spec v' ty'

ssaModule :: Module Int -> SSA (Module SSAID)
ssaModule (Module module_name defss exports) = do
  defss' <- mapM ssaDefGroup defss
  exports' <- mapM ssaExport exports
  return $ Module module_name defss' exports'

computeSSA :: Int               -- ^ First statement ID to use
           -> Int               -- ^ First variable ID to use
           -> Int               -- ^ First SSA ID to use
           -> [(PVar, ParserVarBinding)] -- ^ Predefined variables
           -> Module Int        -- ^ Module to convert
           -> IO (Int, Int, Int, Module SSAID)
           -- ^ (next statement ID, next variable ID, next SSA ID, converted module)
computeSSA next_stmt_id next_var_id next_ssa_id predefined_vars mod = do
  stmt_id_ref <- newIORef next_stmt_id
  var_id_ref <- newIORef next_var_id
  ssa_id_ref <- newIORef next_ssa_id
  let ctx = SSACtx var_id_ref ssa_id_ref stmt_id_ref

  (mod', _, _) <-
    runSSA (ssaModule mod) ctx [globalScope predefined_vars] emptyNLC
  
  next_stmt_id' <- readIORef stmt_id_ref
  next_var_id' <- readIORef var_id_ref
  next_ssa_id' <- readIORef ssa_id_ref
  
  return (next_stmt_id', next_var_id', next_ssa_id', mod')

-- | The global scope, containing predefined variables
globalScope vars = Map.fromList [(v, NotSSA) | (v, _) <- vars]
