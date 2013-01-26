
{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts #-}
module Parser.SSA2
       (SSAID, removeSSAID, externSSAVar,
        SSAVar,
        SSAIDSupply, newSSAIDSupply,
        SSATree(..),
        SSAScope, emptySSAScope, externSSAScope,
        ssaGlobalGroup, ssaExportItem)
where

import Control.Exception
import Control.Monad
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.Trans
import Compiler.Hoopl
import Compiler.Hoopl.GHC(uniqueToInt, lblToUnique)
import Compiler.Hoopl.Passes.Dominator
import qualified Data.Graph.Inductive as FGL
import qualified Data.Graph.Inductive.Graph as FGL
import qualified Data.Graph.Inductive.Query.DFS as FGL
import Data.IORef
import Data.List(find, elemIndex, nub, intercalate)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Typeable
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.MonadLogic
import Common.SourcePos
import Common.Supply
import Common.Worklist
import Parser.ParserSyntax hiding(Stmt(..))
import Parser.Control
import Parser.Dataflow

type instance VarID SSAID = SSAID

type instance FuncBody SSAID = SSATree SSAID

graphBlocks :: CFG AST C C -> LabelMap (Block (LStmt AST) C C)
graphBlocks (GMany NothingO block_map NothingO) = block_map

-- | Get a liveness value that was saved by liveness analysis.
--   It is an error if liveness is not present.
getLiveness :: MLiveness -> Liveness
getLiveness Nothing  = internalError "getLiveness: No liveness information"
getLiveness (Just l) = l

-------------------------------------------------------------------------------

-- | The dominance frontier of a block B is the set of blocks C where
--   B dominates a predecessor of C but does not strictly dominate C
type DomFrontier = LabelMap [Label]

-- | Compute dominators and remove unreachable nodes from the graph
dominators :: Label -> CFG AST C C -> (CFG AST C C, LabelMap Doms)
dominators entry graph = let
  entry_fact = mapSingleton entry domEntry

  -- Dominator analysis removes unreachable blocks from the graph
  (graph', doms, _) =
    runSimpleUniqueMonad $
    analyzeAndRewriteFwd domPass (JustC entry) graph entry_fact
  in (graph', doms)

domFrontier :: CFG AST C C -> LabelMap Doms -> DomFrontier
domFrontier graph dominators =
  mapFromList [(label, frontier label) | label <- mapKeys block_map]
  where
    block_map = graphBlocks graph

    predecessor :: Block (LStmt AST) C C -> Label -> Bool
    b `predecessor` l = l `elem` successors b
    
    l1 `dominates` l2 = let Just dpath = mapLookup l2 dominators
                      in l1 `elem` domPath dpath

    frontier b = [c | pred_block <- mapElems block_map
                      -- B dominates pred_block or B is pred_block
                    , b `dominates` entryLabel pred_block ||
                      b == entryLabel pred_block
                      -- Check all successors of pred_block
                    , c <- successors pred_block
                      -- B does not dominate c
                    , not $ b `dominates` c]

analyzeDominators :: LCFunc AST -> (LabelMap Doms, DomFrontier)
analyzeDominators lfunc =
  let func           = unLoc lfunc
      entry          = cfEntry func  
      graph          = cfBody func
      (graph', doms) = dominators entry graph
      frontier       = domFrontier graph' doms
  in (doms, frontier)

-------------------------------------------------------------------------------

-- | A variable ID assigned by SSA analysis.
--
--   The lexical version is the ID assigned by the parser.
--   The SSA version is an extra ID assigned by SSA analysis.
--
--   IDs of variables defined externally to the module are always 0.
--   Other IDs are numbered starting at 1.
data SSAID = SSAID { lexicalVersion :: {-#UNPACK#-}!Int
                   , ssaVersion     :: {-#UNPACK#-}!Int
                   }
             deriving(Eq, Ord)

instance Show SSAID where
  show (SSAID l v) = "(SSAID " ++ show l ++ " " ++ show v ++ ")"

-- | An SSA variable
type SSAVar = Var SSAID

class Monad m => SSANameMonad m where
  newSSAID :: Int -> m SSAID

newSSAVar :: SSANameMonad m => PVar -> m SSAVar
newSSAVar v = do
  v_id <- newSSAID $ varID v
  return $ Var (varName v) v_id

removeSSAID :: SSAVar -> PVar
removeSSAID v = Var (varName v) (lexicalVersion $ varID v)

externSSAVar :: PVar -> Var SSAID
externSSAVar (Var name i) = Var name (SSAID i 0)

instance Ppr (Var SSAID) where
  ppr v = let ssa_id = varID v
              ssa_text = show (lexicalVersion ssa_id) ++
                         '.' : show (ssaVersion ssa_id)
          in text (varName v ++ '\'' : ssa_text)

newtype SSAIDSupply = SSAIDSupply (Supply Int)

newSSAIDSupply :: IO SSAIDSupply
newSSAIDSupply = liftM SSAIDSupply $ newSupply 0 (1+)

supplySSAID :: SSAIDSupply -> IO Int
supplySSAID (SSAIDSupply s) = supplyValue s

-- | A monad with an ID supply
newtype IDM a = IDM {unIDM :: ReaderT SSAIDSupply IO a}
  deriving(Monad, MonadIO)

runIDM :: IDM a -> SSAIDSupply -> IO a
runIDM m r = runReaderT (unIDM m) r

instance SSANameMonad IDM where
  newSSAID var_id = do
    ssa_supply <- IDM ask
    ssa_id <- liftIO $ supplySSAID ssa_supply
    return $ SSAID {lexicalVersion = var_id, ssaVersion = ssa_id}


-------------------------------------------------------------------------------
-- Data structures for holding phi nodes during SSA

-- | A block has an associated list of incoming edges
type Sources = [Source]

-- | Create an 'IORef' containing @Nothing@ for each source
sourcesToEmptyRefs :: Sources -> IO [IORef (Maybe a)]
sourcesToEmptyRefs xs = forM xs $ \_ -> newIORef Nothing

-- | Assign an 'IORef' indexed by @key@.
--   The given lists of sources and references must have equal length, 
--   and the key must be present in the list.
insertAtSource :: Source -> Sources -> a -> [IORef (Maybe a)] -> IO ()
insertAtSource key keys x refs = go keys refs
  where
    go (k:keys) (ref:refs)
      | key == k  = writeIORef ref (Just x)
      | otherwise = go keys refs
    go _ _ = internalError "insertAtSource: Key not found"

-- | A phi node defines a new SSA variable from the given SSA variables
data Phi = Phi SSAVar [IORef (Maybe SSAVar)]

insertPhiParameter :: [Source] -> Source -> Phi -> SSAVar -> IO ()
insertPhiParameter sources source (Phi _ refs) param =
  insertAtSource source sources param refs

-- | A set of phi nodes, indexed by non-SSA variable
type Phis = Map.Map PVar Phi

emptyPhis :: Map.Map PVar Phi
emptyPhis = Map.empty

-- | Convert a phi map to a list of SSA variable bindings
phisToBindings :: Phis -> [(PVar, SSAVar)]
phisToBindings phis = [(v, v') | (v, Phi v' _) <- Map.toList phis]

-- | A block's phi set identifies how live variables are merged by
--   control flow in a block.
--
--   The list of sources identifies the incoming control flow edges.
--
--   Each merged variable is mapped to a list of SSA source IDs, one
--   for each incoming edge.  The SSA IDs start out undefined, and
--   are assigned during analysis.
data BlockPhi = BlockPhi !Label !Sources !(IORef Phis)

newBlockPhi :: Label -> IO BlockPhi
newBlockPhi label = do
  ref <- newIORef emptyPhis
  return $ BlockPhi label [] ref

insertBlockPhiSource :: Source -> BlockPhi -> BlockPhi
insertBlockPhiSource s (BlockPhi l ss r) = BlockPhi l (s:ss) r

readBlockPhi :: BlockPhi -> IO (Sources, Phis)
readBlockPhi (BlockPhi _ sources ref) = do
  phis <- readIORef ref
  return (sources, phis)

-- | Insert a phi node into a block, if one is not already there.
--   Return 'True' if inserted, 'False' if already present.
insertPhi :: (SSANameMonad m, MonadIO m) => BlockPhi -> PVar -> m Bool
insertPhi (BlockPhi label sources phis_ref) v = do
  phis <- liftIO $ readIORef phis_ref
  if v `Map.member` phis
    then return False
    else do phis' <- insert_phi phis
            liftIO $ writeIORef phis_ref phis'
            return True
  where
    insert_phi phis = do
      v' <- newSSAVar v
      source_refs <- liftIO $ sourcesToEmptyRefs sources
      return $ Map.insert v (Phi v' source_refs) phis 

-- | Read the phi parameters that a given source should pass
readBlockPhiParameters :: Source -> BlockPhi -> IO [SSAVar]
readBlockPhiParameters source (BlockPhi label sources phis_ref) = do 
  phis <- readIORef phis_ref

  -- Find the parameter index corresponding to this source
  let Just source_index = elemIndex source sources

  -- Read the parameter of each phi
  forM (Map.elems phis) $ \(Phi _ refs) -> do
    Just ssavar <- readIORef $ refs !! source_index
    return ssavar

readBlockPhiResults :: BlockPhi -> IO [SSAVar]
readBlockPhiResults (BlockPhi _ _ phis_ref) = do
  phis <- readIORef phis_ref
  return [v | Phi v _ <- Map.elems phis]

-- | A set of phi nodes for each block.  Blocks are identified by their
--   first node's label.
type PhiMap = Map.Map Label BlockPhi

lookupBlockPhi :: Label -> PhiMap -> BlockPhi
lookupBlockPhi l m =
  case Map.lookup l m
  of Just x -> x
     Nothing -> internalError "lookupBlockPhi"

-- | Insert a phi node for the given variable at the given block, if not
--   already present.  Return True if inserted, False if already there.
insertPhiInBlock :: (SSANameMonad m, MonadIO m) =>
                    PhiMap -> Label -> PVar -> m Bool
insertPhiInBlock phi_map block var = do
  let Just block_phi = Map.lookup block phi_map
  insertPhi block_phi var

formatPhiMap :: PhiMap -> IO Doc
formatPhiMap m = liftM vcat $ mapM format_entry $ Map.assocs m
  where
    format_entry (label, block_phi) = do
      (sources, m) <- readBlockPhi block_phi
      let block_name = ppr label <+> brackets (hsep $ pprCommaList sources)
      ssas <- liftM vcat $ mapM format_phi $ Map.assocs m
      return $ block_name $$ nest 4 ssas

    format_phi (v, phi) = do
      phi_doc <- formatPhi phi
      return $ hang (ppr v) 10 phi_doc
      
formatPhi (Phi var source_vars) = do
  sources <- mapM readIORef source_vars
  let sources_doc = punctuate comma $
                    map (maybe (text "?") (text . show)) sources
  return $ text (show var) <+> text "<-" <+> fsep sources_doc

-- | Create a phi map with all phi nodes inserted, but no phi node arguments
--   assigned.
createPhiMap :: CFG AST C C -> Livenesses -> DomFrontier -> IDM PhiMap
createPhiMap graph livenesses frontier = do
  phi_map <- liftIO $ createEmptyPhiMap graph
  populatePhiMap graph livenesses phi_map frontier
  return phi_map

-- | Create a phi map with an empty set of phis for each block
createEmptyPhiMap :: CFG AST C C -> IO PhiMap
createEmptyPhiMap graph = do 
  let block_map = graphBlocks graph

  -- Create map with empty sources
  empty_phis <- create_empty_map $ mapKeys block_map

  -- Insert source edges into the map
  return $ foldr insert_edge empty_phis $ mapElems block_map
  where
    create_empty_map labels = do
      block_phis <- mapM newBlockPhi labels
      return $ Map.fromList $ zip labels block_phis

    insert_edge block phis =
      foldr insert_source phis $ blockOutEdges block

    insert_source (source, label) phis =
      Map.update (Just . insertBlockPhiSource source) label phis

-- | Lift a monadic higher-order function into IDM
liftIDM1 :: ((a -> IO b) -> IO c) -> (a -> IDM b) -> IDM c
liftIDM1 t f = IDM $ ReaderT $ \env -> t (\x -> runIDM (f x) env)

-- TODO: What about redefinitions of function parameters?
populatePhiMap :: CFG AST C C -> Livenesses -> PhiMap -> DomFrontier -> IDM ()
populatePhiMap graph livenesses phi_map frontiers = do
  -- For each pair (label, var)
  -- where block 'label' contains a definition of 'var'
  worklist <- liftIO $ newWorklist definitions
  liftIDM1 (forWorklist worklist) $ \(label, var) -> do

    -- For each node in the dominance frontier of 'label'
    -- that has 'var' as a live-in
    let Just frontier = mapLookup label frontiers
        filtered_frontier = filter (var `live_in` ) frontier
    liftIDM1 (forM_ filtered_frontier) $ \f_label -> do
      -- Insert a phi node here
      updated <- insertPhiInBlock phi_map f_label var

      -- If a new node was inserted, then add this block to the worklist
      when updated $ liftIO $ putWorklist worklist (f_label, var)
  where
    graph_blocks = graphBlocks graph

    -- Is 'v' a live-in of block 'label'?
    v `live_in` label =
      v `Set.member` getLiveness (mapLookup label livenesses)

    -- Get a list of the blocks that define a variable
    definitions :: [(Label, PVar)]
    definitions =
      [(label, v) | (label, defs) <- mapToList block_definitions, v <- defs]
      where
        block_definitions = mapMap block_defs graph_blocks

        -- Get all definitions in a block
        block_defs block =
          Set.toList $ foldBlockNodesF getStmtDefinitions block Set.empty

-------------------------------------------------------------------------------
-- SSA analysis
        
data SSAEnv = 
  SSAEnv 
  { ssaLivenesses :: !Livenesses 
  , ssaPhiMap :: !PhiMap 
  , ssaDomFrontier :: !DomFrontier
  , ssaIDSupply :: !SSAIDSupply
  }

type SSAScope = Map.Map PVar SSAVar

emptySSAScope :: SSAScope
emptySSAScope = Map.empty

-- | Given a list of externally defined variables, create an SSA scope with
--   these variables
externSSAScope :: [PVar] -> SSAScope
externSSAScope vars = Map.fromList [(v, externSSAVar v) | v <- vars]

-- | An SSA construction monad.
--
--   A bind (m >>= k) allows m to update the SSA scope of k; k sees
--   the scope dominated by m.  Use 'inLocalScope' to override this.
newtype SSAM a = SSAM {unSSAM :: RWST SSAEnv () SSAScope IO a}
               deriving(Monad, MonadIO)

-- | Run SSA computation for a local function, using the given
--   function-scope information.
localSSAComputation :: Livenesses
                    -> DomFrontier
                    -> PhiMap
                    -> SSAScope
                    -> SSAM a
                    -> IDM (a, SSAScope)
localSSAComputation livenesses frontier phis scope (SSAM m) =
  IDM $ ReaderT $ \id_supply -> do
    let local_env = SSAEnv livenesses phis frontier id_supply
    (x, scope', _) <- runRWST m local_env scope
    return (x, scope')

globalSSAComputation :: SSAScope -> SSAM a -> IDM (a, SSAScope)
globalSSAComputation scope m =
  localSSAComputation mapEmpty mapEmpty Map.empty scope m

liftIDM :: IDM a -> SSAM a
liftIDM (IDM m) = SSAM $ RWST $ \r s -> do
  x <- runReaderT m (ssaIDSupply r)
  return (x, s, ())

-- | Run the computation in a local scope.  Its changes to the SSA scope
--   are not propagated.
inLocalScope :: SSAM a -> SSAM a
inLocalScope (SSAM m) = SSAM $ do
  scope <- get
  x <- m
  put scope
  return x

getLivenesses :: SSAM Livenesses
getLivenesses = SSAM $ asks ssaLivenesses

getPhiMap :: SSAM PhiMap
getPhiMap = SSAM $ asks ssaPhiMap

getDominanceFrontier :: SSAM DomFrontier
getDominanceFrontier = SSAM $ asks ssaDomFrontier

getSSAIDSupply :: SSAM SSAIDSupply
getSSAIDSupply = SSAM $ asks ssaIDSupply

getSSAScope :: SSAM SSAScope
getSSAScope = SSAM get

modifySSAScope :: (SSAScope -> SSAScope) -> SSAM ()
modifySSAScope f = SSAM $ modify f

instance SSANameMonad SSAM where
  newSSAID var_id = do
    ssa_supply <- SSAM $ asks ssaIDSupply
    ssa_id <- liftIO $ supplySSAID ssa_supply
    return $ SSAID {lexicalVersion = var_id, ssaVersion = ssa_id}

defineSSAVar :: PVar -> SSAM SSAVar
defineSSAVar v = do
  v' <- newSSAVar v
  defineSSAVar' v v'
  return v'

-- | Add an existing binding to the environment
defineSSAVar' :: PVar -> SSAVar -> SSAM ()
defineSSAVar' v v' = modifySSAScope (Map.insert v v')

definePhi :: Phi -> SSAM ()
definePhi (Phi var _) = do
  modifySSAScope (Map.insert (removeSSAID var) var)

-- | Look up the dominance frontier of a given node
lookupDomFrontier :: Label -> SSAM [Label]
lookupDomFrontier l = do
  df <- getDominanceFrontier
  case mapLookup l df of
    Just ls -> return ls
    Nothing -> internalError "lookupDomFrontier: Frontier not found"

lookupSSAVar :: PVar -> SSAM SSAVar
lookupSSAVar v = do
  scope <- getSSAScope
  case Map.lookup v scope of
    Just v' -> return v'
    Nothing -> internalError "lookupSSAVar: No SSA version for variable"

getBlockPhi :: Label -> SSAM BlockPhi
getBlockPhi lab = do
  m <- getPhiMap
  let Just block_phi = Map.lookup lab m
  return block_phi

-- | The class of things that can be SSA-renamed and only have locally scoped
--   variables
class SSAAble a where
  type SSA a
  rename :: a -> SSAM (SSA a)

instance SSAAble a => SSAAble [a] where
  type SSA [a] = [SSA a]
  rename xs = mapM rename xs 

instance SSAAble a => SSAAble (Maybe a) where
  type SSA (Maybe a) = Maybe (SSA a)
  rename Nothing = return Nothing
  rename (Just x) = liftM Just $ rename x

instance SSAAble a => SSAAble (Loc a) where
  type SSA (Loc a) = Loc (SSA a)
  rename (Loc pos x) = Loc pos `liftM` rename x

instance SSAAble (Var AST) where
  type SSA (Var AST) = Var SSAID
  rename = lookupSSAVar

instance SSAAble (Expr AST) where
  type SSA (Expr AST) = Expr SSAID
  rename (Variable v)     = Variable `liftM` rename v
  rename (Literal l)      = return $ Literal l
  rename (Tuple es)       = Tuple `liftM` mapM rename es
  rename (List es)        = List `liftM` mapM rename es
  rename (Unary op e)     = Unary op `liftM` rename e
  rename (Binary op e f)  = Binary op `liftM` rename e `ap` rename f
  rename (Subscript e s)  = Subscript `liftM` rename e `ap` rename s
  rename (Slicing e s)    = Slicing `liftM` rename e `ap` rename s
  rename (ListComp iter)  = ListComp `liftM` rename iter
  rename (Generator iter) = Generator `liftM` rename iter
  rename (Call e es)      = Call `liftM` rename e `ap` rename es
  rename (Cond c t f)     = Cond `liftM`
                                rename c `ap` rename t `ap` rename f
  rename (Lambda ps e)    = withRenamedParameters ps $ \ps' ->
                                Lambda ps' `liftM` rename e
  rename (Let p e f)      = do e' <- rename e
                               withRenamedParameter p $ \p' -> do
                                 f' <- rename f
                                 return $ Let p' e' f'

instance SSAAble (Slice AST) where
  type SSA (Slice AST) = Slice SSAID
  rename (SliceSlice pos l u s) =
    SliceSlice pos `liftM` rename l `ap` rename u `ap` rename s
  rename (ExprSlice e) = ExprSlice `liftM` rename e

instance SSAAble (IterFor AST) where
  type SSA (IterFor AST) = IterFor SSAID
  rename (IterFor pos ps source comp) = do
    source' <- rename source
    withRenamedParameters ps $ \ps' -> do
      comp' <- rename comp
      return $ IterFor pos ps' source' comp'

instance SSAAble (IterIf AST) where
  type SSA (IterIf AST) = IterIf SSAID
  rename (IterIf pos cond comp) =
    IterIf pos `liftM` rename cond `ap` rename comp

instance SSAAble (IterLet AST) where
  type SSA (IterLet AST) = IterLet SSAID
  rename (IterLet pos p rhs comp) = do
    rhs' <- rename rhs
    withRenamedParameter p $ \p' -> do
      comp' <- rename comp
      return $ IterLet pos p' rhs' comp'

instance SSAAble (Comprehension AST) where
  type SSA (Comprehension AST) = Comprehension SSAID
  rename (CompFor i) = CompFor `liftM` rename i
  rename (CompIf i) = CompIf `liftM` rename i
  rename (CompLet i) = CompLet `liftM` rename i
  rename (CompBody x) = CompBody `liftM` rename x

type WithRenamed t a = t AST -> (t SSAID -> SSAM a) -> SSAM a

withRenamedVar :: WithRenamed Var a
withRenamedVar v k = inLocalScope $ defineSSAVar v >>= k

withRenamedParameter :: WithRenamed Parameter a
withRenamedParameter (Parameter v ann) k = do
  ann' <- rename ann
  withRenamedVar v $ \v' -> k (Parameter v' ann')

withRenamedParameter (TupleParam ps) k =
  withRenamedParameters ps $ \ps' -> k (TupleParam ps')

withRenamedParameters :: [Parameter AST] -> ([Parameter SSAID] -> SSAM a) -> SSAM a
withRenamedParameters ps k = withMany withRenamedParameter ps k

withForallAnnotation Nothing k = k Nothing

withForallAnnotation (Just (ForallAnnotation qvars cst)) k =
  withRenamedParameters qvars $ \qvars' -> do
    cst' <- rename cst
    k (Just (ForallAnnotation qvars' cst'))

-- | SSA-rename a parameter whose variables are visible to later statements
ssaParameter :: Parameter AST -> SSAM (Parameter SSAID)
ssaParameter (Parameter v ann) = do
  ann' <- rename ann
  v' <- defineSSAVar v
  return $ Parameter v' ann'

ssaParameter (TupleParam ps) = do
  ps' <- mapM ssaParameter ps
  return $ TupleParam ps'

-- | Add a function definition to the environment
ssaDefineFunction :: LCFunc AST -> SSAM SSAVar
ssaDefineFunction fdef = defineSSAVar (sigName $ cfSignature $ unLoc fdef)

-- | Perform SSA on a function definition.  The function should have been
--   added to the environment.
ssaFunctionDefinition :: LCFunc AST -> SSAVar -> SSAM (LCFunc SSAID)
ssaFunctionDefinition (Loc pos fdef) fname =
  withForallAnnotation ann $ \ann' -> do
    r_ann' <- rename r_ann
    withRenamedParameters params $ \params' -> do
      let sig' = FunSig fname ann' pragma params' r_ann'
      let entry = cfEntry fdef
          Just livenesses = cfLivenesses fdef
      ssa_tree <- ssaGraph' livenesses entry (cfBody fdef)
      return $ Loc pos $ CFunc sig' Nothing entry ssa_tree
  where
    FunSig _ ann pragma params r_ann = cfSignature fdef

ssaStmt :: LStmt AST e x -> SSAM (LStmt SSAID e x)
ssaStmt (LStmt (Loc pos stmt)) =
  case stmt
  of Assign params e -> do
       e' <- rename e
       params' <- ssaParameter params
       re_loc' $ Assign params' e'
     DefGroup fs _ -> do
       f_names <- mapM ssaDefineFunction fs
       fs' <- zipWithM ssaFunctionDefinition fs f_names
       re_loc' $ DefGroup fs' Nothing
     Assert es ->
       re_loc $ Assert `liftM` rename es
     Require v e ->
       re_loc $ Require `liftM` rename v `ap` rename e
     Target l _ ->
       re_loc' $ Target l Nothing
     If e t f -> do
       e' <- rename e
       re_loc' $ If e' (change_type t) (change_type f)
     Jump l ->
       re_loc' $ Jump (change_type l)
     Return e ->
       re_loc $ Return `liftM` rename e
  where
    re_loc :: SSAM (Stmt SSAID e x) -> SSAM (LStmt SSAID e x)
    re_loc x = liftM (LStmt . Loc pos) x
    re_loc' :: Stmt SSAID e x -> SSAM (LStmt SSAID e x)
    re_loc' x = return (LStmt $ Loc pos x)

    change_type :: Flow a -> Flow b
    change_type (Flow l Nothing) = Flow l Nothing

-- | An SSA dominator tree arrangement of labeled blocks.
--
--   Tree children are organized into recursive groups, with later
--   groups referencing earlier ones.
data SSATree id = SSATree (Block (LStmt id) C C) [[SSATree id]]

graphToTree :: LabelMap Doms -> CFG AST C C -> SSATree AST
graphToTree dominators graph = make_tree $ tree $ mapToList dominators
  where
    graph_blocks = graphBlocks graph
    get_block l = case mapLookup l graph_blocks
                  of Just l -> l
                     Nothing -> internalError "graphToTree"

    make_tree (Dominates Entry [t]) = make_tree t
    make_tree (Dominates (Labelled n) ts) =
      let children = map make_tree ts
      in SSATree (get_block n) (treeSCCs children)

treeToGraph :: SSATree id -> CFG id C C
treeToGraph tree = GMany NothingO (mapFromList $ blocks tree) NothingO
  where
    blocks (SSATree b ts) = (entryLabel b, b) : concatMap blocks (concat ts)

-- | Organize a collection of trees into SCCs by how they reference each other.
--   A < B if A references B.
treeSCCs :: [SSATree AST] -> [[SSATree AST]]
treeSCCs trees = let
  nodes = [label_id $ entryLabel b | SSATree b _ <- trees]
  edges = [(src, dst) | SSATree b children <- trees
                      , let src = label_id $ entryLabel b
                      , target <- nub $ childLabelRefs2 children
                      , let dst = label_id target
                      , dst `elem` nodes]
  graph = FGL.mkUGraph nodes edges :: FGL.Gr () ()

  -- Get the SCCs, with the most reachable nodes at the beginning
  sccs = reverse $ FGL.scc graph
  in [[get_tree n | n <- scc] | scc <- sccs]
  where
    label_id b = uniqueToInt $ lblToUnique b
    get_tree n = case find label_is_n trees
                 of Just t -> t
                    Nothing -> internalError "treeSCCs"
      where
        label_is_n (SSATree b _) = label_id (entryLabel b) == n

childLabelRefs2 :: [[SSATree AST]] -> [Label]
childLabelRefs2 = concatMap childLabelRefs1

childLabelRefs1 :: [SSATree AST] -> [Label]
childLabelRefs1 = concatMap childLabelRefs

childLabelRefs :: SSATree AST -> [Label]
childLabelRefs (SSATree b children) = successors b ++ childLabelRefs2 children

-- | Perform SSA on a control flow graph
ssaGraph' :: Livenesses -> Label -> CFG AST C C -> SSAM (SSATree SSAID)
ssaGraph' livenesses entry graph = do
  scope <- getSSAScope
  liftIDM $ ssaGraph scope livenesses entry graph

ssaGraph :: SSAScope -> Livenesses -> Label -> CFG AST C C
         -> IDM (SSATree SSAID)
ssaGraph scope livenesses entry graph = do
  -- Compute global information
  let (graph', doms) = dominators entry graph
      dom_frontier   = domFrontier graph' doms 
      dom_tree       = graphToTree doms graph'
  phi_map <- createPhiMap graph' livenesses dom_frontier

  -- Run SSA
  (ssa_tree, _) <- localSSAComputation livenesses dom_frontier phi_map scope $
                   ssaTree dom_tree

  -- Insert phi nodes
  ssa_tree_with_phi <- liftIO $ insertPhisIntoBlocks phi_map ssa_tree

  return ssa_tree_with_phi

-- | Perform SSA on a subtree of the dominator tree
ssaTree :: SSATree AST -> SSAM (SSATree SSAID)
ssaTree (SSATree block children) = inLocalScope $ do
  block' <- ssaBlock block
  children' <- mapM (mapM ssaTree) children
  return $ SSATree block' children'

-- | Perform SSA on one control flow block
ssaBlock :: Block (LStmt AST) C C -> SSAM (Block (LStmt SSAID) C C)
ssaBlock block = do
  let (JustC first, middle, JustC last) = blockToNodeList block
      label = entryLabel block
      out_edges = blockOutEdges block

  -- Update environment with phi node definitions
  ssaDefineBlockPhi label
  first' <- ssaStmt first
  middle' <- mapM ssaStmt middle
  last' <- ssaStmt last

  -- Update the dominance frontier of this block
  mapM_ ssaUpdateDefs out_edges

  return $ blockOfNodeList (JustC first', middle', JustC last')

-- | Add SSA definitions to the environment for each phi node in the block
ssaDefineBlockPhi label = do
  -- Look up the phi bindings
  block_phi <- getBlockPhi label
  (_, phis) <- liftIO $ readBlockPhi block_phi

  -- Add them to the SSA environment
  sequence_ [defineSSAVar' v v' | (v, v') <- phisToBindings phis]

-- | Add parameters to the phi nodes of each outgoing edge
ssaUpdateDefs :: (Source, Label) -> SSAM ()
ssaUpdateDefs (source, successor_label) = do
  -- Get phis of this node
  (succ_sources, succ_phis) <-
    liftIO . readBlockPhi =<< getBlockPhi successor_label

  -- For each phi, insert the current SSA version as a parameter
  forM_ (Map.toList succ_phis) $ \(var, phi) -> do
    ssa_var <- lookupSSAVar var
    liftIO $ insertPhiParameter succ_sources source phi ssa_var


insertPhisIntoBlocks phi_map (SSATree block children) = do
  block' <- insertPhisIntoBlock phi_map block
  children' <- mapM (mapM (insertPhisIntoBlocks phi_map)) children
  return $ SSATree block' children'

insertPhisIntoBlock phi_map block = do
  let (JustC first, middle, JustC last) = blockToNodeList block
      label = entryLabel first
  first' <- insertPhisIntoFirst phi_map label first
  last' <- insertPhisIntoLast phi_map label last
  return $ blockOfNodeList (JustC first', middle, JustC last')

-- | Add phi parameter list onto incoming control flow
insertPhisIntoFirst :: PhiMap -> Label -> LStmt SSAID C O
                    -> IO (LStmt SSAID C O)
insertPhisIntoFirst phi_map label (LStmt (Loc pos (Target l Nothing))) = do
  params <- readBlockPhiResults $ lookupBlockPhi label phi_map
  return $ LStmt $ Loc pos (Target l (Just params))

-- | Add phi annotations onto outgoing control flow
insertPhisIntoLast :: PhiMap -> Label -> LStmt SSAID O C
                   -> IO (LStmt SSAID O C)
insertPhisIntoLast phi_map label (LStmt (Loc pos stmt)) =
  case stmt
  of If cond t_flow f_flow -> do
       t_flow' <- insertPhisIntoFlow phi_map (Source label TruePath) t_flow
       f_flow' <- insertPhisIntoFlow phi_map (Source label FalsePath) f_flow
       return $ LStmt $ Loc pos $ If cond t_flow' f_flow'
     Jump flow -> do
       flow' <- insertPhisIntoFlow phi_map (Source label JumpPath) flow
       return $ LStmt $ Loc pos $ Jump flow'
     Return e ->
       return $ LStmt $ Loc pos stmt

insertPhisIntoFlow phi_map source (Flow target Nothing) = do
  ssa_vars <- readBlockPhiParameters source $ lookupBlockPhi target phi_map
  return $ Flow target (Just ssa_vars)

-- | Do SSA on one global function group
ssaGlobalGroup :: SSAIDSupply -> SSAScope -> [LCFunc AST]
               -> IO ([LCFunc SSAID], SSAScope)
ssaGlobalGroup supply scope fdefs =
  with_supply $ globalSSAComputation scope $ do
    vs <- mapM ssaDefineFunction fdefs
    zipWithM ssaFunctionDefinition fdefs vs
  where
    with_supply m = runIDM m supply

ssaExportItem :: SSAIDSupply -> SSAScope -> ExportItem AST
              -> IO (ExportItem SSAID, SSAScope)
ssaExportItem supply scope export =
  with_supply $ globalSSAComputation scope $ do
    v <- rename $ exportVar export
    t <- rename $ exportType export
    return $ ExportItem { exportPos = exportPos export
                        , exportSpec = exportSpec export
                        , exportVar = v
                        , exportType = t}
  where
    with_supply m = runIDM m supply
