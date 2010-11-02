{-| This pass eliminates record value types from the IR by converting
--  record types to multiple-value-passing.  Also, record-valued constants
--  are inlined.
--
-- Record types in parameters or returns are unpacked to multiple parameters 
-- or return values.
-}

{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving #-}
module LowLevel.RecordFlattening
       (flattenGlobalValue, flattenGlobalValues, flattenRecordTypes)
where

import Control.Monad
import Control.Monad.Reader
import qualified Data.IntMap as IntMap
import Data.Maybe

import Gluon.Common.Error
import Gluon.Common.MonadLogic
import Gluon.Common.Supply
import Gluon.Common.Identifier
import LowLevel.Types
import LowLevel.Record
import LowLevel.Syntax
import LowLevel.Build
import SystemF.Builtins
import Globals

-- | An expansion of a variable.  A variable's expansion may be unknown if
--   it was imported.
data Expansion = Expansion [Val] | UnknownExpansion

-- | During flattening, each variable is associated with its equivalent
-- flattened list of variables.
type Expansions = IntMap.IntMap Expansion

-- | Expand a use of variable into a list of values.
expand :: Expansions -> Var -> [Val]
expand m v = expand_var v
  where
    -- Expand a variable, recursively.
    expand_var v =
      case IntMap.lookup (fromIdent $ varID v) m
      of Just (Expansion vs) -> concatMap (expand_value_from v) vs
         Just UnknownExpansion -> [VarV v]
         Nothing -> internalError "expand: No information for variable"
        
    -- Expand a value that was created from 'v'.  If the variable doesn't 
    -- expand to itself, then expand recursively.  (It's necessary to check 
    -- for expanding-to-itself to avoid an infinite loop.)
    expand_value_from v value =
      case value
      of VarV v' | v /= v' -> expand_var v'

         -- A variable never expands to a record type or lambda function
         LamV {} -> internalError "expand: Unexpected lambda function"
         RecV {} -> internalError "expand: Unexpected record type"
         
         -- Other values require no further expansion
         _ -> [value]

-------------------------------------------------------------------------------
         
newtype RF a = RF {runRF :: ReaderT RFEnv IO a} deriving(Monad, Functor)

data RFEnv = RFEnv { rfVarSupply :: {-# UNPACK #-}!(IdentSupply Var)
                   , rfExpansions :: !Expansions
                   }

instance Supplies RF (Ident Var) where
  fresh = RF $ ReaderT $ \env -> supplyValue $ rfVarSupply env

assign :: Var -> [Val] -> RF a -> RF a
assign v expansion m = RF $ local (insert_assignment v expansion) $ runRF m
  where
    insert_assignment v expansion env =
      env {rfExpansions =
              IntMap.insert (fromIdent $ varID v) (Expansion expansion) $
              rfExpansions env}

expandVar :: Var -> RF [Val]
expandVar v = RF $ asks get_expansion
  where
    get_expansion env = expand (rfExpansions env) v

-- | If a parameter variable is a record, rename it to some new parameter
-- variables
defineParam :: ParamVar -> ([ParamVar] -> RF a) -> RF a
defineParam v k =
  case varType v
  of PrimType UnitType -> assign_to []
     PrimType t        -> assign_to [v] -- No change
     RecordType rec    -> defineRecord rec assign_to
  where
    assign_to expanded_list =
      assign v (map VarV expanded_list) $ k expanded_list
       
-- | Define a list of parameter variables
defineParams :: [ParamVar] -> ([ParamVar] -> RF a) -> RF a
defineParams vs k = withMany defineParam vs $ k . concat

-- | Count the number of expanded values a record field constitutes
expandedFieldSize :: StaticField -> Int
expandedFieldSize f = length $ flattenFieldType $ fieldType f

-- | Create a new parameter variable for each expanded record field
defineRecord :: StaticRecord -> ([ParamVar] -> RF a) -> RF a
defineRecord record k = do
  expanded_vars <- mapM (newAnonymousVar . PrimType) $ flattenRecordType record
  foldr assign_expanded_var (k expanded_vars) expanded_vars
  where
    -- The parameter variables expand to themselves
    assign_expanded_var v k = assign v [VarV v] k

flattenTypeList :: [ValueType] -> [PrimType]
flattenTypeList xs = concatMap flattenType xs

flattenValueTypeList :: [ValueType] -> [ValueType]
flattenValueTypeList xs = map PrimType $ flattenTypeList xs

flattenFunctionType :: FunctionType -> FunctionType
flattenFunctionType ft =
  mkFunctionType (ftIsPrim ft)
  (flattenValueTypeList $ ftParamTypes ft)
  (flattenValueTypeList $ ftReturnTypes ft)

flattenType :: ValueType -> [PrimType]
flattenType (PrimType UnitType) = []
flattenType (PrimType pt) = [pt]
flattenType (RecordType rt) = flattenRecordType rt

flattenRecordType :: StaticRecord -> [PrimType]
flattenRecordType rt =
  concatMap flattenFieldType $ map fieldType $ recordFields rt
    
flattenFieldType (PrimField UnitType) = []
flattenFieldType (PrimField pt) = [pt]
flattenFieldType (RecordField record_type) = flattenRecordType record_type

flattenValList :: [Val] -> RF [Val]
flattenValList vs = liftM concat $ mapM flattenVal vs

flattenVal :: Val -> RF [Val]
flattenVal value =
  case value
  of VarV v -> expandVar v
     RecV _ vals -> liftM concat $ mapM flattenVal vals
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

-- | Convert a flattened value list to one that doesn't contain any lambda 
--   functions, by assigning lambda functions to temporary variables.  The
--   returned list contains variables in place of lambda functions.
bindLambdas :: [Val] -> RF (Stm -> Stm, [Val])
bindLambdas values = do
  (bindings, new_values) <- mapAndUnzipM bind_lambda values
  return (foldr (.) id bindings, new_values)
  where
    bind_lambda value =
      case value
      of VarV _ -> no_change
         RecV _ _ ->
           -- We were given a value that wasn't flattened
           internalError "bindLambdas"
         LitV _ -> no_change
         LamV f -> do
           -- Assign the lambda function to a variable
           fun_var <- newAnonymousVar (PrimType OwnedType)
           return (LetE [fun_var] $ ValA [value], VarV fun_var)
      where
        no_change = return (id, value)

flattenStm :: Stm -> RF Stm
flattenStm statement =
  case statement
  of LetE [v] (PackA _ vals) next_statement -> do
       -- Copy-propagate the values by assigning them directly to 'v'
       -- in the expansion mapping
       vals' <- flattenValList vals
       (lambda_bindings, vals'') <- bindLambdas vals'
       assign v vals'' $ fmap lambda_bindings $ flattenStm next_statement
     LetE vs (UnpackA record val) next_statement -> do
       -- Copy-propagate the values by assigning them directly to each of 'vs'
       -- in the expansion mapping
       let expanded_vs_sizes = map expandedFieldSize $ recordFields record
       vals <- flattenVal val
       assign_variables vs expanded_vs_sizes vals next_statement
     LetE vs atom next_statement -> do
       atom' <- flattenAtom atom
       defineParams vs $ \vs' ->
         fmap (assignment vs' atom') $ flattenStm next_statement
     LetrecE defs next_statement ->
       defineParams [v | FunDef v _ <- defs] $ \_ -> do
         defs' <- mapM flatten_def defs
         fmap (LetrecE defs') $ flattenStm next_statement
     SwitchE val alts -> do
       val' <- flattenSingleVal val
       alts' <- mapM flatten_alt alts
       return $ SwitchE val' alts' 
     ReturnE atom ->
       fmap ReturnE $ flattenAtom atom
  where
    flatten_def (FunDef v f) = do
      f' <- flattenFun f
      return $ FunDef v f'

    flatten_alt (lit, stm) = do
      stm' <- flattenStm stm
      return (lit, stm')

    -- Create a sequence of \'Let\' statements from the given LHS and RHS.
    -- The parts of the statement have been flattened.
    -- If the statement is a simple multiple assignment statement, then
    -- split it into multiple statements.
    assignment vs (ValA vals)
      | length vs /= length vals = internalError "flattenStm"
      | otherwise =
          -- Split into a sequence of statements
          \stm -> foldr (\(v, x) s -> LetE [v] (ValA [x]) s) stm $ zip vs vals

    assignment vs atom = LetE vs atom

    -- Process a record unpacking statement.  Substitute each record field
    -- (which will be a variable or literal) in place of the variable from
    -- the unpacking statement.
    assign_variables (v:vs) (size:sizes) values stm = do
      -- Take the values that will be assigned to 'v'
      let (v_values, values') = splitAt size values
      unless (length v_values == size) unpack_size_mismatch
      assign v v_values $ assign_variables vs sizes values' stm
    
    assign_variables [] [] [] stm = flattenStm stm
    assign_variables [] [] _  _   = unpack_size_mismatch
    assign_variables _  _  [] _   = unpack_size_mismatch

    unpack_size_mismatch =
      internalError "flattenStm: Record size mismatch when unpacking parameters"

flattenFun :: Fun -> RF Fun
flattenFun fun =
  defineParams (funParams fun) $ \params -> do
    let returns = flattenValueTypeList $ funReturnTypes fun
    body <- flattenStm $ funBody fun
    return $! if isPrimFun fun 
              then primFun params returns body
              else if isClosureFun fun
                   then closureFun params returns body
                   else internalError "flattenFun"

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

flattenImport :: Import -> RF Import
flattenImport (ImportClosureFun ep) =
  let ep' =
        case ep
        of EntryPoints ty arity dir exa ine dea inf glo ->
             let ty'    = flattenFunctionType ty
                 arity' = length $ ftParamTypes ty'
             in EntryPoints ty' arity' dir exa ine dea inf glo
  in return $ ImportClosureFun ep'

flattenImport (ImportPrimFun v t) =
  return $ ImportPrimFun v (flattenFunctionType t)

flattenImport (ImportData v initializer) = do
  initializer' <- case initializer 
                  of Nothing -> return Nothing
                     Just vs -> fmap Just $ flattenValList vs
  return $ ImportData v initializer'

flattenRecordTypes :: Module -> IO Module
flattenRecordTypes mod =
  withTheLLVarIdentSupply $ \var_supply -> do
    let import_map = makeImportMap (moduleImports mod)
        env = RFEnv var_supply import_map
    runReaderT (runRF flatten_module) env
  where
    flatten_module = do
      imports' <- mapM flattenImport (moduleImports mod)
      (fun_defs', data_defs') <-
        flattenTopLevel (moduleFunctions mod) (moduleData mod)
      return $ mod { moduleImports = imports'
                   , moduleFunctions = fun_defs'
                   , moduleData = data_defs'}

makeImportMap imports =
  IntMap.fromList [(fromIdent $ varID $ importVar v, UnknownExpansion)
                  | v <- imports]

-------------------------------------------------------------------------------


flattenGlobalValues :: [Val] -> [Val]
flattenGlobalValues vs = concatMap flattenGlobalValue vs

-- | An exported record flattening function for flattening global values.
-- Global variables never expand to records, and may not contain lambda
-- expressions.
flattenGlobalValue :: Val -> [Val]
flattenGlobalValue value =
  case value
  of VarV v -> [value]
     RecV _ vals -> flattenGlobalValues vals
     LitV UnitL -> []
     LitV _ -> [value]
     LamV f -> internalError "flattenGlobalValue: Unexpected lambda function"
