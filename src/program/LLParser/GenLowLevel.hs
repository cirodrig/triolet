{-| Generation of low-level code from an AST.

The main responsibilities of this module are to resolve names, infer types,
flatten complex expressions into sequences of statements, and compute field
offsets.  There are two kinds of names: variable names and type names.
The currently visible names are stored in an 'Env' value and found by
'lookupEntity'.  The environment also stores type information.

The type of any expression can be inferred from its fields and the
environment.  When an expression (or another AST component that returns
a value) is processed, its type is returned along with its LowLevel
translation.  Type information in the environment associated with record types
is used to compute field offsets.

Expression flattening basically uses the same mechanism as "LowLevel.Build".
Subexpressions are emitted as separate statements and bound to temporary
variables whenever necessary.
-}
{-# LANGUAGE RecursiveDo, EmptyDataDecls, TypeFamilies, FlexibleInstances, 
    ViewPatterns, Rank2Types #-}
module LLParser.GenLowLevel(generateLowLevelModule)
where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Writer
import Data.List
import qualified Data.Map as Map
import System.FilePath

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.Supply 
import LLParser.AST
import LowLevel.Types
import LowLevel.Build
import LowLevel.Record hiding(Field, recordFields)
import qualified LowLevel.Syntax as LL
import Globals

data Resolved

type instance VarName Resolved = LL.Var
type instance RecordName Resolved = ResolvedRecord

-- | A resolved function, data, or top-level definition
data ResolvedDef =
    ResolvedFunctionDef LL.FunDef
  | ResolvedDataDef LL.DataDef
  | ResolvedRecordDef -- ^ Record definitions are erased after translation

partitionResolvedDefinitions :: [ResolvedDef] -> ([LL.FunDef], [LL.DataDef])
partitionResolvedDefinitions defs = part defs id id
  where
    part (def:defs) fun dat =
      case def
      of ResolvedFunctionDef f -> part defs (fun . (f:)) dat
         ResolvedDataDef d     -> part defs fun (dat . (d:))
         ResolvedRecordDef     -> part defs fun dat

    part [] fun dat = (fun [], dat [])

newtype RecordIdent = RecordIdent String
data ResolvedRecord =
  ResolvedRecord 
  { resolvedRecordName :: !RecordIdent 
  , resolvedRecordFields :: [FieldDef Resolved] 
  , resolvedRecordType :: StaticRecord
  }

data DictEntry =
    VarEntry !LL.Var
    -- | A record definition.  The record's name and fields are included for
    --   lookup.
  | RecordEntry {-# UNPACK #-}!ResolvedRecord

-- | A dictionary associates each source code name with a variable or record
-- type.
type Dict = Map.Map String DictEntry

emptyDict = Map.empty

data Scope =
    RecScope
    { completeDict :: Dict        -- ^ Fully built dictionary
    , partialDict :: !Dict        -- ^ Partially built dictionary
    }
  | NonRecScope !Dict

-------------------------------------------------------------------------------

-- | The name resolution moand
newtype NR a =
  NR {runNR :: NREnv -> Env -> Errors -> IO (a, Env, Errors)}

data NREnv =
  NREnv
  { varIDSupply :: {-# UNPACK #-}!(Supply (Ident LL.Var))
  , sourceModuleName  :: !ModuleName
  }

type Env = [Scope]
type Errors = [String] -> [String]

instance Functor NR where
  fmap f m = NR $ \ctx env errs -> do
    (x, env', errs') <- runNR m ctx env errs
    return (f x, env', errs')

instance Monad NR where
  {-# INLINE return #-}
  {-# INLINE (>>=) #-}
  return x = NR (\_ env errs -> return (x, env, errs))
  m >>= k = NR $ \ctx env errs -> do
    (x, env', errs') <- runNR m ctx env errs
    runNR (k x) ctx env' errs'

instance Supplies NR (Ident LL.Var) where
  fresh = NR $ \ctx env errs -> do
    x <- supplyValue (varIDSupply ctx)
    return (x, env, errs)

addError :: String -> Errors -> Errors
addError err errs = (err :) . errs

addErrorMaybe :: Maybe String -> Errors -> Errors
addErrorMaybe err errs = maybe id (:) err . errs

throwErrorMaybe :: Maybe String -> NR ()
throwErrorMaybe err = NR $ \_ env errs -> 
  return ((), env, addErrorMaybe err errs)

-- | Enter a recursive scope.  Start building a local dictionary; pass the
-- final dictionary back in as input when done.
enterRec :: NR a -> NR a
enterRec m = NR $ \ctx env errs -> mdo
  let init_local_scope =
        RecScope { completeDict = partialDict (head env')
                 , partialDict = emptyDict
                 }
  (x, env', errs') <- runNR m ctx (init_local_scope : env) errs
  return (x, tail env', errs')

-- | Enter a nonrecursvie scope.
enterNonRec :: NR a -> NR a
enterNonRec m = NR $ \ctx env errs -> do
  (x, env', errs') <- runNR m ctx (NonRecScope emptyDict : env) errs
  return (x, tail env', errs')

-- | Add a definition to the current scope.  If the definition conflicts
-- with an existing definition, an error is reported.
defineEntity :: String -> DictEntry -> NR ()
defineEntity name value = NR $ \ctx env errs ->
  case env
  of scope : scopes ->
       case scope
       of RecScope {partialDict = pd}
            | name `Map.member` pd ->
                -- The same name was defined repeatedly in a recursive
                -- scope.  Report an error.
                let error_message = "Name '" ++ name ++ "' is redefined"
                in return ((), env, addError error_message errs)
            | otherwise ->
                -- Add the definition to the partial dictionary.
                let scope' = scope {partialDict = Map.insert name value $
                                                  partialDict scope}
                in return ((), scope' : scopes, errs)
          NonRecScope d -> 
            -- Add the definition to the non-recursive dictionary.
            let scope' = NonRecScope (Map.insert name value d)
            in return ((), scope' : scopes, errs)

-- | Look up a name.  If the name is not found, then an error is reported, 
-- the returned entry is undefined, and False is returned.  The returned
-- entry and boolean value should be used lazily.
lookupEntity :: String -> NR (DictEntry, Bool)
lookupEntity name = NR $ \_ env errs ->
  -- Ensure that the returned values are non-strict
  let (entry, is_defined, err) = lookup_name env
  in return ((entry, is_defined), env, addErrorMaybe err errs)
  where
    lookup_name (scope : scopes) =
      let dict =
            case scope
            of RecScope {completeDict = cd} -> cd
               NonRecScope d -> d
      in case Map.lookup name dict
         of Just e  -> (e, True, Nothing)
            Nothing -> lookup_name scopes
    
    -- If the entire environment has been searched, then fail
    lookup_name [] = (internalError "lookupEntity",
                      False,
                      Just $ "Undefined name: '" ++ name ++ "'")

-- | Create a new variable.  The definition is not added to the environment.
createVar :: String -> LL.ValueType -> NR LL.Var
createVar name ty = do
  module_name <- NR $ \env ctx errs -> return (sourceModuleName env, ctx, errs)
  let label = pgmLabel module_name name
  LL.newVar (Just label) ty

-- | Add a variable definition to the environment
defineVar :: LL.Var -> NR ()
defineVar v =
  let name = case LL.varName v
             of Just lab -> labelUnqualifiedName lab 
                Nothing -> internalError "defineVar"
  in defineEntity name (VarEntry v)

-- | Process a definition of a name, creating a new variable.
createAndDefineVar :: String -> LL.ValueType -> NR LL.Var
createAndDefineVar name ty = do
  v <- createVar name ty
  defineVar v
  return v

lookupVar :: String -> NR LL.Var
lookupVar name = do
  (entry, is_defined) <- lookupEntity name
  throwErrorMaybe $
    if is_defined
    then case entry
         of VarEntry _ -> Nothing
            _ -> Just $ "Not a variable: '" ++ name ++ "'"
    else Nothing
  return $ case entry of ~(VarEntry v) -> v

lookupRecord :: String -> NR ResolvedRecord
lookupRecord name = do
  (entry, is_defined) <- lookupEntity name
  throwErrorMaybe $ 
    if is_defined
    then case entry
         of RecordEntry {} -> Nothing
            _ -> Just $ "Not a record: '" ++ name ++ "'"
    else Nothing
  return $ case entry of ~(RecordEntry record) -> record

-- | Define a new record type
defineRecord :: RecordName Parsed -> [StaticFieldType] -> [FieldDef Resolved]
             -> NR ()
defineRecord name field_types fields =
  let record =
        ResolvedRecord (RecordIdent name) fields (staticRecord field_types)
  in defineEntity name (RecordEntry record)

-------------------------------------------------------------------------------

type GenNR a = Gen NR a

transformGenNR :: (forall a. NR a -> NR a) -> GenNR a -> GenNR a
transformGenNR f m = WriterT $ f $ runWriterT m

resolveType :: Type Parsed -> GenNR (Type Resolved)
resolveType ty =
  case ty
  of PrimT pt   -> return $ PrimT pt
     RecordT nm -> lift $ do
       record <- lookupRecord nm
       return $ RecordT record
     BytesT size align -> do
       size' <- resolveExprVar size
       align' <- resolveExprVar align
       return $ BytesT (VarE size') (VarE align')

-- | Resolve a type without generating any code
resolvePureType :: Type Parsed -> NR (Type Resolved)
resolvePureType ty =
  case ty
  of PrimT pt   -> return $ PrimT pt
     RecordT nm -> do
       record <- lookupRecord nm
       return $ RecordT record
     BytesT size align -> do
       (size', _, _) <- resolvePureExpr size
       (align', _, _) <- resolvePureExpr align
       return $ BytesT size' align'

resolveValueType :: Type Parsed -> GenNR LL.ValueType
resolveValueType ty = fmap convertToValueType $ resolveType ty

resolvePureValueType :: Type Parsed -> NR LL.ValueType
resolvePureValueType ty = fmap convertToValueType $ resolvePureType ty

-- | Convert a type to a value type.
convertToValueType :: Type Resolved -> LL.ValueType
convertToValueType ty =
  case ty
  of PrimT pt -> LL.PrimType pt
     RecordT record -> LL.RecordType $ resolvedRecordType record
     _ -> error "Expecting a value type"

convertToFieldType :: Type Resolved -> StaticFieldType
convertToFieldType ty =
  case ty
  of PrimT pt -> PrimField pt
     RecordT r -> RecordField $ resolvedRecordType r
     BytesT size align -> BytesField (fromIntExpr size) (fromIntExpr align)

resolveFieldDef :: FieldDef Parsed -> NR (StaticFieldType, FieldDef Resolved)
resolveFieldDef (FieldDef ty nm) = do
  ty' <- resolvePureType ty
  return (convertToFieldType ty', FieldDef ty' nm)

-- | From a record field specifier, get the field's offset and data type.
resolveField :: Field Parsed -> GenNR (LL.Val, LL.ValueType)
resolveField (Field record field_names mcast) = do
  -- Get field offset and type
  record_type <- lift $ lookupRecord record
  let ~(offset, field_type) =
        foldl go_to_field (0, RecordT record_type) field_names
  
  -- Cast the field type if appropriate
  field_type' <-
    case mcast
    of Nothing -> return $ convertToValueType field_type
       Just t  -> resolveValueType t
  let offset_value = nativeIntV offset
      value_type = convertToValueType field_type
  return (offset_value, value_type)
  where
    go_to_field (offset, RecordT record_type) field_name =
      -- Find the field with this name
      case findIndex (\(FieldDef _ nm) -> nm == field_name) $
           resolvedRecordFields record_type
      of Just ix ->
           let offset' = offset + fieldOffset (resolvedRecordType record_type !!: ix)
               FieldDef field_type _ = resolvedRecordFields record_type !! ix
           in (offset', field_type)
         _ ->
           error "Record type does not have field"

    go_to_field (_, _) _ =
      error "Field access only valid for record types"

-- | Perform name resolution on an expression.  The expression must be a
-- variable or literal.  It will become a value.
resolvePureExpr :: Expr Parsed -> NR (Expr Resolved, LL.Val, LL.ValueType)
resolvePureExpr expr =
  case expr
  of VarE vname -> do
       v <- lookupVar vname
       return (VarE v, LL.VarV v, LL.varType v)
     IntLitE ty n -> do
       ty' <- resolvePureType ty
       let llty = convertToValueType ty'
       return (IntLitE ty' n, LL.LitV $ mkIntLit llty n, llty)
     FloatLitE ty n -> do
       ty' <- resolvePureType ty
       let llty = convertToValueType ty'
       return (FloatLitE ty' n, LL.LitV $ mkFloatLit llty n, llty)
     

-- | Perform name resolution on expressions.  To create variables, we have to
-- get expressions' types at the same time.
resolveExpr :: Expr Parsed -> GenNR (LL.Atom, [LL.ValueType])
resolveExpr expr =
  case expr
  of VarE vname -> lift $ do
       v <- lookupVar vname
       return (LL.ValA [LL.VarV v], [LL.varType v])
     IntLitE ty n -> do
       ty' <- resolveValueType ty
       return (LL.ValA [LL.LitV $ mkIntLit ty' n], [ty'])
     FloatLitE ty n -> do
       ty' <- resolveValueType ty
       return (LL.ValA [LL.LitV $ mkFloatLit ty' n], [ty'])
     RecordE nm fields -> do
       record <- lift $ lookupRecord nm
       let record_type = resolvedRecordType record
       fields' <- mapM resolveExprValue fields
       return (LL.PackA record_type fields', [LL.RecordType record_type])
     FieldE base fld -> do
       (fld_offset, _) <- resolveField fld
       base' <- resolveExprValue base
       return (LL.PrimA LL.PrimAddP [base', fld_offset], [LL.PrimType PointerType])
     LoadFieldE base fld -> do
       (fld_offset, fld_ty) <- resolveField fld
       base' <- resolveExprValue base
       return (LL.PrimA (LL.PrimLoad fld_ty) [base', fld_offset], [fld_ty])
     CallE rtypes f args -> do
       rtypes' <- mapM resolveValueType rtypes
       f' <- resolveExprValue f
       args' <- mapM resolveExprValue args
       return (LL.CallA f' args', rtypes')
     PrimCallE rtypes f args -> do
       rtypes' <- mapM resolveValueType rtypes
       f' <- resolveExprValue f
       args' <- mapM resolveExprValue args
       return (LL.CallA f' args', rtypes')

resolveExpr1 :: Expr Parsed -> GenNR (LL.Atom, LL.ValueType)
resolveExpr1 e = do
  (atom, types) <- resolveExpr e
  case types of
    [ty] -> return (atom, ty)
    _ -> internalError "Expecting a single-valued expression"

atomValue :: (LL.Atom, LL.ValueType) -> GenNR (LL.Val, LL.ValueType)
atomValue (atom, ty) =
  case atom
  of LL.ValA [val] -> return (val, ty)
     _ -> do
       val <- emitAtom1 ty atom
       return (val, ty)

resolveExprValues :: Expr Parsed -> GenNR [LL.Val]
resolveExprValues e = do
  (atom, types) <- resolveExpr e
  case atom of
    LL.ValA values -> return values
    _ -> emitAtom types atom
       
resolveExprValue :: Expr Parsed -> GenNR LL.Val
resolveExprValue e = do
  vals <- resolveExprValues e
  case vals of
    [val] -> return val
    _ -> error "Expecting one return value from expression"

resolveExprVar :: Expr Parsed -> GenNR LL.Var
resolveExprVar e = do
  value <- resolveExprValue e
  case value of
    LL.VarV v -> return v
    _ -> do
      let ty = LL.valType value
      tmpvar <- lift $ LL.newAnonymousVar ty
      bindAtom1 tmpvar (LL.ValA [value])
      return tmpvar

resolveAtom :: Atom Parsed -> GenNR (LL.Atom, [LL.ValueType])
resolveAtom (ValA [expr]) = resolveExpr expr

-- To resolve an expression list, generate values for the individual
-- expressions and then return a group of values
resolveAtom (ValA exprs) = do
  (unzip -> (vals, types)) <- mapM (atomValue <=< resolveExpr1) exprs
  return (LL.ValA vals, types)

resolveAtom (IfA cond true false) = do
  -- Evaluate the condition
  cond_val <- resolveExprValue cond 
  (true_block, true_types) <- getBlock' $ resolveBlock true
  (false_block, false_types) <- getBlock' $ resolveBlock false

  -- True and false types should match
  let atom = LL.SwitchA cond_val [ (LL.BoolL True, true_block)
                                 , (LL.BoolL False, false_block)]
  return (atom, true_types)

resolveStmt :: Stmt Parsed -> GenNR ()
resolveStmt (LetS lvals atom) = do
  -- Convert the RHS of the assignment; find out how many return values
  -- there are
  (atom', types) <- resolveAtom atom
  unless (length types == length lvals) $
    error "resolveStmt: Wrong number of binders"
    
  -- Choose variables for each return value; determine what additional
  -- code to generate if any
  (unzip3 -> (dsts, deferred_stores, bindings)) <-
    lift $ zipWithM resolveLValue lvals types 
  
  -- Generate the statement
  bindAtom dsts atom'

  -- Generate code to store values
  sequence_ deferred_stores
  
  -- Add bindings to the environment
  lift $ sequence_ bindings

-- | Do name resolution on an lvalue.
--
-- If the lvalue is a simple variable, then just translate and assign
-- the variable.  If it's a store expression, then assign to a temporary
-- variable, then store it.
resolveLValue lval ty =
  case lval
  of VarL var_name -> do
       v <- createVar var_name ty
       return (v, return (), defineVar v)

     StoreFieldL base fld -> do
       v <- LL.newAnonymousVar ty
       return (v, store_value v base fld, return ())
  where
    store_value v base fld = do
      -- Compute the base and offset
      base' <- resolveExprValue base
      (offset, _) <- resolveField fld
      
      -- Generate a store
      primStoreOff ty base' offset (LL.VarV v)

resolveBlock :: Block Parsed -> GenNR (LL.Atom, [LL.ValueType])
resolveBlock (Block stmts atom) = transformGenNR enterNonRec $ do
  mapM_ resolveStmt stmts
  resolveAtom atom

defineParameter :: Parameter Parsed -> NR LL.Var
defineParameter (Parameter ty nm) = do
  ty' <- resolvePureValueType ty
  createAndDefineVar nm ty'

resolveFunctionDef :: FunctionDef Parsed -> NR LL.FunDef
resolveFunctionDef fdef = do
  -- Define the function variable
  let function_type = if functionIsProcedure fdef
                      then LL.PrimType PointerType
                      else LL.PrimType OwnedType
  fvar <- createAndDefineVar (functionName fdef) function_type

  -- Create the function
  fun <- enterNonRec $ do
    -- Bind function parameters
    params <- mapM defineParameter $ functionParams fdef
    
    -- Generate the function body
    (body, body_return_types) <- execBuild' $ resolveBlock $ functionBody fdef
    
    -- Translate the return types (should match body's return types)
    return_types <- mapM resolvePureValueType $ functionReturns fdef
    
    return $! if functionIsProcedure fdef
              then LL.primFun params return_types body
              else LL.closureFun params return_types body

  -- Return the function definition
  return $ LL.FunDef fvar fun

resolveRecordDef rdef = do
  unless (null $ recordParams rdef) $
    internalError "Not implemented: parameterized records"
  
  (unzip -> (field_types, fs)) <- mapM resolveFieldDef $ recordFields rdef
  defineRecord (recordName rdef) field_types fs

resolveDef :: Def Parsed -> NR ResolvedDef
resolveDef (FunctionDefEnt fdef) =
  fmap ResolvedFunctionDef $ resolveFunctionDef fdef

resolveDef (RecordDefEnt rdef) = do
  resolveRecordDef rdef
  return ResolvedRecordDef

-- | Resolve a set of top-level definitions
resolveTopLevelDefs :: [Def Parsed] -> NR LL.Module
resolveTopLevelDefs defs = enterRec $ do
  rdefs <- mapM resolveDef defs
  let (fun_defs, data_defs) = partitionResolvedDefinitions rdefs
  return $ LL.Module fun_defs data_defs

generateLowLevelModule :: FilePath -> [Def Parsed] -> IO LL.Module
generateLowLevelModule module_name defs =
  withTheLLVarIdentSupply $ \var_ids -> do
    let ctx = NREnv var_ids (moduleName $ takeFileName module_name)
        global_scope = []
    (mod, _, errs) <- runNR (resolveTopLevelDefs defs) ctx global_scope id

    case errs [] of
      [] -> return mod
      xs -> do mapM_ putStrLn xs
               fail "Errors detected while parsing input"

-------------------------------------------------------------------------------
-- Functions for creating LowLevel expressions

mkIntLit :: LL.ValueType -> Integer -> LL.Lit
mkIntLit ty n =
  case ty
  of LL.PrimType (IntType sgn sz) -> LL.IntL sgn sz n
     _ -> error "Invalid integer type"

mkFloatLit :: LL.ValueType -> Double -> LL.Lit
mkFloatLit ty n =
  case ty
  of LL.PrimType (FloatType sz) -> LL.FloatL sz n
     _ -> error "Invalid floating-point type"

fromIntExpr :: Expr Resolved -> Int
fromIntExpr (IntLitE _ n) = fromIntegral n
fromIntExpr _ = error "Expecting literal value"
