{-| This pass eliminates record value types from functions.
-- Record-typed variables are converted to multiple variables.
-- Record types in parameters or returns are unpacked to multiple parameters 
-- or return values.
-}

{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving #-}
module Pyon.LowLevel.RecordFlattening(flattenRecordTypes)
where

import Control.Monad
import Control.Monad.Reader
import qualified Data.IntMap as IntMap

import Gluon.Common.Error
import Gluon.Common.MonadLogic
import Gluon.Common.Supply
import Gluon.Common.Identifier
import Pyon.LowLevel.Types
import Pyon.LowLevel.Record
import Pyon.LowLevel.Syntax
import Pyon.Globals

-- | During flattening, each variable is associated with its equivalent
-- flattened list of variables.
type Expansion = IntMap.IntMap [Var]

-- | Expand a use of variable into a list of its fields.
expand :: Expansion -> Var -> [Var]
expand m v = exp v
  where
    -- | Expand a variable.  If the expansion is not the variable itself,
    -- then expand recursively.
    exp v =
      case IntMap.lookup (fromIdent $ varID v) m
      of Just vs | vs /= [v] -> concatMap exp vs
                 | otherwise -> vs
         Nothing -> internalError "expand: No information for variable"

-------------------------------------------------------------------------------
         
newtype RF a = RF {runRF :: ReaderT RFEnv IO a} deriving(Monad)

data RFEnv = RFEnv { rfVarSupply :: {-# UNPACK #-}!(IdentSupply Var)
                   , rfExpansions :: !Expansion
                   }

instance Supplies RF (Ident Var) where
  fresh = RF $ ReaderT $ \env -> supplyValue $ rfVarSupply env

assign :: Var -> [Var] -> RF a -> RF a
assign v expansion m = RF $ local (insert_assignment v expansion) $ runRF m
  where
    insert_assignment v expansion env =
      env {rfExpansions = IntMap.insert (fromIdent $ varID v) expansion $
                          rfExpansions env}

expandVar :: Var -> RF [Var]
expandVar v = RF $ asks get_expansion
  where
    get_expansion env =
      case IntMap.lookup (fromIdent $ varID v) $ rfExpansions env
      of Nothing -> internalError "expandVar: No expansion for variable"
         Just vs -> vs

-- | If a parameter variable is a record, rename it to some new parameter
-- variables
defineParam :: ParamVar -> ([ParamVar] -> RF a) -> RF a
defineParam v k = do
  expanded_var <-
    case varType v
    of PrimType UnitType -> return []
       PrimType t        -> return [v]        -- No change
       RecordType rec    -> defineRecord rec
  assign v expanded_var $ k expanded_var
       
-- | Define a list of parameter variables
defineParams :: [ParamVar] -> ([ParamVar] -> RF a) -> RF a
defineParams vs k = withMany defineParam vs $ k . concat

-- | Create a new parameter variable for each expanded record field
defineRecord :: StaticRecord -> RF [ParamVar]
defineRecord record =
  mapM (newAnonymousVar . PrimType) $ flattenRecordType record

flattenTypeList :: [ValueType] -> [PrimType]
flattenTypeList xs = concatMap flattenType xs

flattenValueTypeList :: [ValueType] -> [ValueType]
flattenValueTypeList xs = map PrimType $ flattenTypeList xs

flattenType :: ValueType -> [PrimType]
flattenType (PrimType UnitType) = []
flattenType (PrimType pt) = [pt]
flattenType (RecordType rt) = flattenRecordType rt

flattenRecordType :: StaticRecord -> [PrimType]
flattenRecordType rt =
  concatMap flattenField $ map fieldType $ recordFields rt
  where
    flattenField (PrimField UnitType) = []
    
    flattenField (PrimField pt) = [pt]

    flattenField (RecordField _ record_type) =
      flattenRecordType record_type

flattenValList :: [Val] -> RF [Val]
flattenValList vs = liftM concat $ mapM flattenVal vs

flattenVal :: Val -> RF [Val]
flattenVal value =
  case value
  of VarV v -> liftM (map VarV) $ expandVar v
     RecV _ vals -> liftM concat $ mapM flattenVal vals
     ConV _ -> return [value]
     LitV UnitL -> return []
     LitV _ -> return [value]
     LamV f -> do f' <- flattenFun f
                  return [LamV f']

-- | Flatten a value.  The result must be a single value.
flattenSingleVal :: Val -> RF Val
flattenSingleVal v = do
  vlist <- flattenVal v
  case vlist of
    [v'] -> return v'
    _ -> internalError "flattenSingleVal"

flattenAtom :: Atom -> RF Atom
flattenAtom atom =
  case atom
  of ValA vs ->
       ValA `liftM` flattenValList vs
     CallA op vs ->
       CallA `liftM` flattenSingleVal op `ap` flattenValList vs
     PrimCallA op vs ->
       PrimCallA `liftM` flattenSingleVal op `ap` flattenValList vs
     PrimA prim vs ->
       PrimA prim `liftM` flattenValList vs
     PackA _ vals ->
       -- Return a tuple of values
       ValA `liftM` flattenValList vals
     UnpackA _ v ->
       -- The argument expands to a tuple of values.  Return the tuple.
       ValA `liftM` flattenVal v
     SwitchA v alts ->
       SwitchA `liftM` flattenSingleVal v `ap` mapM flattenAlt alts
  where
    flattenAlt (lit, block) = do
      block' <- flattenBlock block
      return (lit, block')

flattenStm :: Stm -> (Stm -> RF a) -> RF a
flattenStm statement k =
  case statement
  of LetE vs atom -> do
       atom' <- flattenAtom atom
       defineParams vs $ \vs' -> k $ LetE vs' atom'
     LetrecE defs ->
       defineParams [v | FunDef v _ <- defs] $ \_ -> do
         k . LetrecE =<< mapM flatten_def defs
  where
    flatten_def (FunDef v f) = do
      f' <- flattenFun f
      return $ FunDef v f'

flattenBlock :: Block -> RF Block
flattenBlock (Block stms atom) =
  withMany flattenStm stms $ \stms' -> do
    atom' <- flattenAtom atom
    return $ Block stms' atom'

flattenFun :: Fun -> RF Fun
flattenFun (Fun params returns body) =
  defineParams params $ \params' -> do
    let returns' = flattenValueTypeList returns
    body' <- flattenBlock body
    return $ Fun params' returns' body'

flattenTopLevel :: [FunDef] -> [DataDef] -> RF ([FunDef], [DataDef])
flattenTopLevel fun_defs data_defs =
  -- Ensure that all globals are defined
  defineParams [v | FunDef v _ <- fun_defs] $ \_ ->
  defineParams [v | DataDef v _ _ <- data_defs] $ \_ -> do
    -- Flatten the globals
    fun_defs' <- mapM flatten_def fun_defs
    data_defs' <- mapM flattenDataDef data_defs
    return (fun_defs', data_defs')
  where
    flatten_def (FunDef v f) = do
      f' <- flattenFun f
      return $ FunDef v f'
  
-- | Change a data definition to a flat structure type
flattenDataDef :: DataDef -> RF DataDef
flattenDataDef (DataDef v record vals) = do
  val' <- flattenValList vals
  let record' = staticRecord $ map PrimField $ flattenRecordType record
  return $ DataDef v record' val'

flattenRecordTypes :: Module -> IO Module
flattenRecordTypes mod =
  withTheLLVarIdentSupply $ \var_supply -> do
    let env = RFEnv var_supply IntMap.empty
    runReaderT (runRF flatten_module) env
  where
    flatten_module = do
      (fun_defs, data_defs) <-
        flattenTopLevel (moduleFunctions mod) (moduleData mod)
      return $ Module fun_defs data_defs
  