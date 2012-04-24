{-|

This pass eliminates record value types from the IR by converting
record types to multiple-value-passing.  Also, record-valued constants
are inlined.

After record flattening, records may only appear as
parameters or return values of exported functions, and in @pack@ and
@unpack@ statements.  Later stages of the compiler expect to never see a
record as an argument or result of a function call.

Record types in parameters or returns are unpacked to multiple parameters 
or return values.
-}

{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, ViewPatterns #-}
module LowLevel.RecordFlattening
       (flattenGlobalValue, flattenGlobalValues, flattenRecordTypes)
where

import Prelude hiding(mapM)
import Control.Monad hiding(mapM)
import Control.Monad.Reader hiding(mapM)
import qualified Data.IntMap as IntMap
import Data.Maybe
import Data.Traversable(mapM)

import Common.Error
import Common.MonadLogic
import Common.Supply
import Common.Identifier
import LowLevel.CodeTypes
import LowLevel.Records
import LowLevel.Syntax
import LowLevel.Build
import Export
import Globals

-- | The signatures of exported variables.  If a variable is exported,
--   record flattening is performed differently. 
type ExportMap = IntMap.IntMap ExportSig

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
  of PrimType t        -> assign_to [v] -- No change
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
  expanded_vars <- mapM (newAnonymousVar . PrimType) $
                   flattenRecordType record
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
  mkFunctionType (ftConvention ft)
  (flattenValueTypeList $ ftParamTypes ft)
  (flattenValueTypeList $ ftReturnTypes ft)

-- TODO: Flattening types is the identity function, don't do anything
flattenType :: ValueType -> [PrimType]
flattenType (PrimType pt) = [pt]
flattenType (RecordType rt) = flattenRecordType rt

flattenRecordType :: StaticRecord -> [PrimType]
flattenRecordType rt =
  concatMap flattenFieldType $ map fieldType $ recordFields rt

flattenFieldType (PrimField pt) = [pt]
flattenFieldType (RecordField record_type) = flattenRecordType record_type

flattenValList :: [Val] -> RF [Val]
flattenValList vs = liftM concat $ mapM flattenVal vs

flattenVal :: Val -> RF [Val]
flattenVal value =
  case value
  of VarV v -> expandVar v
     RecV _ vals -> liftM concat $ mapM flattenVal vals
     LitV _ -> return [value]

-- | Flatten a value.  The result must be a single value.
flattenSingleVal :: Val -> RF Val
flattenSingleVal v = do
  vlist <- flattenVal v
  case vlist of
    [v'] -> return v'
    _ -> internalError "flattenSingleVal"

-- | Flatten an atom.  Return the new atom.
--
--   Some atoms whose operands are records expand to multiple statements.
--   The statements are returned, and should precede the atom in the new code.
flattenAtom :: Atom -> RF (Stm -> Stm, Atom)
flattenAtom atom =
  case atom
  of ValA vs ->
       return_atom $ ValA `liftM` flattenValList vs
     CallA conv op vs ->
       return_atom $
       CallA conv `liftM` flattenSingleVal op `ap` flattenValList vs
     -- Eliminate a load of a unit value
     PrimA (PrimLoad m (PrimType UnitType)) _ ->
       return (id, ValA [LitV UnitL])
     -- If loading a record, load its parts individually
     PrimA (PrimLoad m (RecordType rec_type)) vs -> do
       [ptr, off] <- flattenValList vs
       flattenLoad m rec_type ptr off
     -- Eliminate a store of a unit value
     PrimA (PrimStore m (PrimType UnitType)) _ ->
       return (id, ValA [])
     -- If storing a record, load its parts individually
     PrimA (PrimStore m (RecordType rec_type)) vs ->
       flattenStore m rec_type =<< flattenValList vs
     PrimA prim vs ->
       return_atom $ PrimA prim `liftM` flattenValList vs
     PackA _ vals ->
       -- Return a tuple of values
       return_atom $ ValA `liftM` flattenValList vals
     UnpackA _ v ->
       -- The argument expands to a tuple of values.  Return the tuple.
       return_atom $ ValA `liftM` flattenVal v
  where
    return_atom m = do atom <- m
                       return (id, atom)

-- Flatten a load of a record by loading its fields individually
flattenLoad :: Mutability -> StaticRecord -> Val -> Val -> RF (Stm -> Stm, Atom)
flattenLoad op_mutable record_type ptr off = do
  -- Compute (ptr ^+ off)
  (compute_base, base) <- pointerOffsetCode ptr off

  -- Load each field into a new variable
  let fields = recordFields $ flattenStaticRecord record_type
  (codes, field_vars) <- mapAndUnzipM (load_field base) fields
  return (compute_base . foldr (.) id codes, ValA $ map VarV field_vars)
  where
    load_field base fld =
      case fieldType fld
      of PrimField pt -> do
           v <- newAnonymousVar (PrimType pt)
           let mutable = case op_mutable
                         of Mutable -> Mutable
                            Constant -> fieldMutable fld
               atom = PrimA (PrimLoad mutable (PrimType pt))
                      [base, nativeIntV $ fieldOffset fld]
           return (LetE [v] atom, v)
         _ -> internalError "flattenLoad"
  
flattenStore op_mutable record_type (ptr : off : values) = do
  -- Compute (ptr ^+ off)
  (compute_base, base) <- pointerOffsetCode ptr off

  -- Store each field
  let store_field fld val =
        let offset = nativeIntV $ fieldOffset fld
            mutable = case op_mutable
                      of Mutable -> Mutable
                         Constant -> fieldMutable fld
            pt = case fieldType fld
                 of PrimField t -> t
                    _ -> internalError "flattenStore"
        in LetE [] $ PrimA (PrimStore mutable (PrimType pt)) [base, offset, val]

      fields = recordFields $ flattenStaticRecord record_type      
      code = foldr (.) id $ zipWith store_field fields values

  return (compute_base . code, ValA [])

pointerOffsetCode ptr off
  | isZeroLit off = return (id, ptr)
  | otherwise = do
      ptr' <- newAnonymousVar (PrimType PointerType)
      return (LetE [ptr'] $ PrimA PrimAddP [ptr, off], VarV ptr')

flattenStm :: Stm -> RF Stm
flattenStm statement =
  case statement
  of LetE [v] (PackA _ vals) next_statement -> do
       -- Copy-propagate the values by assigning them directly to 'v'
       -- in the expansion mapping
       vals' <- flattenValList vals
       assign v vals' $ flattenStm next_statement
     LetE vs (UnpackA record val) next_statement -> do
       -- Copy-propagate the values by assigning them directly to each of 'vs'
       -- in the expansion mapping
       let expanded_vs_sizes = map expandedFieldSize $ recordFields record
       vals <- flattenVal val
       assign_variables vs expanded_vs_sizes vals next_statement
     LetE vs atom next_statement -> do
       (atom_statements, atom') <- flattenAtom atom
       defineParams vs $ \vs' -> do
         next_statement' <- flattenStm next_statement
         return (atom_statements $ assignment vs' atom' next_statement')
     LetrecE (NonRec def) next_statement -> do
       def' <- flatten_def def
       stm' <- defineParam (definiendum def) $ \_ -> flattenStm next_statement
       return (LetrecE (NonRec def') stm')
     LetrecE (Rec defs) next_statement ->
       defineParams (map definiendum defs) $ \_ -> do
         defs' <- mapM flatten_def defs
         fmap (LetrecE (Rec defs')) $ flattenStm next_statement
     SwitchE val alts -> do
       val' <- flattenSingleVal val
       alts' <- mapM flatten_alt alts
       return $ SwitchE val' alts' 
     ReturnE atom -> do
       (atom_statements, atom') <- flattenAtom atom
       return (atom_statements $ ReturnE atom')
     ThrowE val -> do
       val' <- flattenSingleVal val
       return $ ThrowE val'
  where
    flatten_def (Def v f) = do
      f' <- flattenFun f
      return $ Def v f'

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

    unpack_size_mismatch :: forall a. a
    unpack_size_mismatch =
      internalError "flattenStm: Record size mismatch when unpacking parameters"

flattenFun :: Fun -> RF Fun
flattenFun fun =
  defineParams (funParams fun) $ \params -> do
    let returns = flattenValueTypeList $ funReturnTypes fun
    body <- flattenStm $ funBody fun
    return $! mkFun (funConvention fun) (funInlineRequest fun) (funFrameSize fun) params returns body

-- | Flatten a function that will be exported.
--   Some kinds of records will actually be passed as records (like C structs) 
--   rather than flattened out into multiple parameters.
flattenExportedFun :: ExportSig -> Fun -> RF Fun
flattenExportedFun export_sig fun =
  case export_sig
  of CExportSig (CSignature domain range) -> 
       flattenExportedCFun domain range fun

     CXXExportSig (CXXSignature _ domain range) ->
       -- Don't flatten parameters of C++ functions
       flattenFun fun

     PyonExportSig ->
       -- Flatten the same way as an ordinary function
       flattenFun fun

flattenExportedCFun param_types return_type fun
  | not $ isPrimFun fun =
    internalError "flattenExportedFun: Cannot export this function to C"
  | otherwise =
    -- Call 'defineParams' to get the parameters seen by the function body
    defineParams (funParams fun) $ \_ -> do
      let returns = flattenValueTypeList $ funReturnTypes fun
      body <- flattenStm $ funBody fun
      
      -- Generate parameter-manipulating code
      (param_code, params) <-
        flattenExportedParams param_types (funParams fun)
      let body2 = param_code body
      return $! primFun params returns body2

-- | Perform flattening on an exported parameter list.
--   Generate the flattened, exported parameter list and the code that
--   turns the exported parameters into fully flattened parameters.
--
--   The exported parameters must have been defined so that their fully
--   flattened equivalents can be looked up.
flattenExportedParams :: [ExportDataType] -> [ParamVar]
                      -> RF (Stm -> Stm, [ParamVar])
flattenExportedParams exported_types original_params = do
  (unzip -> (codes, new_params)) <-
    zipWithM flattenExportedParam exported_types original_params
  return (foldr (.) id codes, concat new_params)

flattenExportedParam :: ExportDataType -> ParamVar
                     -> RF (Stm -> Stm, [ParamVar])
flattenExportedParam etype original_param = do
  -- Get the variables that this parameter was expanded to
  expanded_values <- expandVar original_param
  let xparams = map from_var expanded_values

  let no_change' = no_change xparams
  case etype of
    ListET _ _ -> no_change'
    TupleET _ -> no_change'
    ArrayET _ _ _ -> no_change'
    PyonNoneET -> no_change'
    PyonIntET -> no_change'
    PyonFloatET -> no_change'
    PyonBoolET -> no_change'
    FunctionET _ _ -> unpack_record cClosureRecord xparams
  where
    -- No flattening is performed for this parameter.
    -- Verify that the parameter hasn't been expanded.
    no_change xparams =
      case xparams
      of [xparam] | xparam == original_param -> return (id, [xparam])
         _ -> internalError "flattenExportedParam"

    -- This parameter is passed as a (flat) record, then unpacked before
    -- executing the function body.
    unpack_record record xparams = do
      new_param <- newAnonymousVar (RecordType record)
      let unpack_stm = LetE xparams $ UnpackA record (VarV new_param)
      return (unpack_stm, [new_param])

    -- Parameter variables always expand to a sequence of variables
    from_var (VarV v) = v
    from_var _ = internalError "flattenExportedParam: Unexpected value"

flattenTopLevel :: ExportMap -> [Group GlobalDef] -> RF [Group GlobalDef]
flattenTopLevel exports defs = do
  flatten_groups defs
  where
    flatten_groups (NonRec def : defss) = do
      def' <- flatten def
      defss' <- defineParam (globalDefiniendum def) $ \_ ->
        flatten_groups defss
      return (NonRec def' : defss')
    
    flatten_groups (Rec defs : defss) =
      defineParams (map globalDefiniendum defs) $ \_ -> do
        defs' <- mapM flatten defs
        defss' <- flatten_groups defss
        return (Rec defs' : defss')
    
    flatten_groups [] = return []

    flatten (GlobalFunDef (Def v f)) = do
      f' <- case IntMap.lookup (fromIdent $ varID v) exports
            of Nothing  -> flattenFun f
               Just sig -> flattenExportedFun sig f
      return $ GlobalFunDef $ Def v f'
  
    flatten (GlobalDataDef d) = fmap GlobalDataDef $ flattenDataDef d

flattenStaticData :: StaticData -> RF StaticData
flattenStaticData (StaticData val) =
  case val
  of RecV recd vals -> do
       -- Create a flattened record
       vals' <- flattenValList vals
       return $ StaticData $ RecV (flattenStaticRecord recd) vals'
     LitV _ ->
       -- Literals are already flattened
       return $ StaticData val

-- | Change a data definition to a flat structure type
flattenDataDef :: DataDef -> RF DataDef
flattenDataDef (Def v sd) = do
  sd' <- flattenStaticData sd
  return $ Def v sd'

flattenImport :: Import -> Import
flattenImport (ImportClosureFun ep Nothing) =
  let ep' =
        case ep
        of EntryPoints ty arity dir vec exa ine inf glo ->
             let ty'    = flattenFunctionType ty
                 arity' = length $ ftParamTypes ty'
             in EntryPoints ty' arity' dir vec exa ine inf glo
  in ImportClosureFun ep' Nothing

flattenImport (ImportPrimFun v t Nothing) =
  ImportPrimFun v (flattenFunctionType t) Nothing

flattenImport (ImportData v Nothing) =
  ImportData v Nothing

-- Imported things should not have a function/data definition attached now
flattenImport _ = internalError "flattenImport: Unexpected import definition"

flattenRecordTypes :: Module -> IO Module
flattenRecordTypes mod =
  withTheLLVarIdentSupply $ \var_supply -> do
    let import_map = makeImportMap $ moduleImports mod
        env = RFEnv var_supply import_map
    runReaderT (runRF flatten_module) env
  where
    exports = IntMap.fromList [(fromIdent $ varID v, sig)
                              | (v, sig) <- moduleExports mod]
    flatten_module = do
      let imports = map flattenImport $ moduleImports mod
      defs <- flattenTopLevel exports (moduleGlobals mod)
      return $ mod { moduleImports = imports
                   , moduleGlobals = defs}

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
     LitV _ -> [value]
