{-| Generation of low-level code from an AST.

The main responsibilities of this module are to resolve names, infer types,
flatten complex expressions into sequences of statements, and compute field
offsets.  There are two kinds of names: variable names and type names.
The currently visible names are stored in an 'Env' value and found by
'lookupEntity'.  The environment also stores type information.

Inter-module name resolution is accomplished with the help of explicit
importing and exporting of external symbols.  As in C, declarations of 
external symbols are assumed to be correct without verifying that the
external definition matches the local declaration.   Definitions of externally
visible symbols whose names match the builtins in "LowLevel.Builtins" are
changed to reference the corresponding built-in variable.  Only externally
visible symbols are changed to reference builtins.

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
import LowLevel.Builtins
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
    -- | Externally defined or externally visible global variables
  , externalVariables :: ![LL.Var]
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

getSourceModuleName :: NR ModuleName 
getSourceModuleName = NR $ \env ctx errs ->
  return (sourceModuleName env, ctx, errs)

getExternalVars :: NR [LL.Var]
getExternalVars = NR $ \env ctx errs ->
  return (externalVariables env, ctx, errs)

addError :: String -> Errors -> Errors
addError err errs = (err :) . errs

addErrorMaybe :: Maybe String -> Errors -> Errors
addErrorMaybe err errs = maybe id (:) err . errs

-- | If the argument is a 'Just' value, report the string as an error.
-- The argument is used lazily.
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
--
-- A module name may optionally be specified; if not given, it defaults to the
-- current input file's module.
createVar :: Maybe ModuleName -> String -> Maybe String -> LL.ValueType
          -> NR LL.Var
createVar mmodule_name name ext_name ty = do
  module_name <- 
    case mmodule_name
    of Nothing -> getSourceModuleName
       Just n -> return n
  let label = pgmLabel module_name name
  LL.newVar (Just label) ext_name ty

-- | Create an externally defined variable.
createBuiltinVar :: String -> String -> LL.ValueType -> NR LL.Var
createBuiltinVar name ext_name ty = do
  let label = pgmLabel builtinModuleName name
  LL.newBuiltinVar label ext_name ty


-- | Create a global variable in the current module.  If the variable has
-- already been declared, return the declared variable instead of creating
-- something.
createGlobalVar :: VarName Parsed -> LL.ValueType -> NR LL.Var
createGlobalVar name ty = do
  -- Was this variable name declared to be external?
  external_vars <- getExternalVars
  case find is_name external_vars
    of Nothing ->
         -- Not external; create a new variable
         createVar Nothing name Nothing ty
       Just evar 
         | ty /= LL.varType evar ->
             error "Type of external declaration does not match type of variable definition"
         | otherwise -> return evar -- Return the already created variable
  where
    -- Check if variable's unqualified name matches given name
    is_name v =
      case LL.varName v
      of Just nm -> name == labelUnqualifiedName nm
         Nothing -> False

-- | Add a variable definition to the environment
defineVar :: LL.Var -> NR ()
defineVar v =
  let name = case LL.varName v
             of Just lab -> labelUnqualifiedName lab 
                Nothing -> internalError "defineVar"
  in defineEntity name (VarEntry v)

-- | Process a definition of a name, creating a new variable.
createAndDefineVar :: String -> Maybe String -> LL.ValueType -> NR LL.Var
createAndDefineVar name ext_name ty = do
  v <- createVar Nothing name ext_name ty
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
     BoolLitE b ->
       return (BoolLitE b, LL.LitV $ LL.BoolL b, LL.PrimType BoolType)

-- | Perform name resolution on expressions.  To create variables, we have to
-- get expressions' types at the same time.
--
-- The expression is returned as an atom.  If possible, the expression is
-- also returned as a value.
resolveExpr :: Expr Parsed -> GenNR (Maybe LL.Val, LL.Atom, [LL.ValueType])
resolveExpr expr =
  case expr
  of VarE vname -> lift $ do
       v <- lookupVar vname
       return_value (LL.VarV v) (LL.varType v)
     IntLitE ty n -> do
       ty' <- resolveValueType ty
       return_value (LL.LitV $ mkIntLit ty' n) ty'
     FloatLitE ty n -> do
       ty' <- resolveValueType ty
       return_value (LL.LitV $ mkFloatLit ty' n) ty'
     BoolLitE b ->
       return_value (LL.LitV $ LL.BoolL b) (LL.PrimType BoolType)
     RecordE nm fields -> do
       record <- lift $ lookupRecord nm
       let record_type = resolvedRecordType record
       (map fst -> fields') <- mapM resolveExprValue fields
       return_atom (LL.PackA record_type fields') [LL.RecordType record_type]
     FieldE base fld -> do
       (fld_offset, _) <- resolveField fld
       (base', _) <- resolveExprValue base
       return_atom (LL.PrimA LL.PrimAddP [base', fld_offset]) [LL.PrimType PointerType]
     LoadFieldE base fld -> do
       (fld_offset, fld_ty) <- resolveField fld
       (base', _) <- resolveExprValue base
       return_atom (LL.PrimA (LL.PrimLoad fld_ty) [base', fld_offset]) [fld_ty]
     DerefE {} -> error "Store expression not valid here"
     LoadE ty base -> do
       ty' <- resolveValueType ty
       (base', _) <- resolveExprValue base
       return_atom (LL.PrimA (LL.PrimLoad ty') [base', nativeIntV 0]) [ty']
     CallE rtypes f args -> do
       rtypes' <- mapM resolveValueType rtypes
       (f', _) <- resolveExprValue f
       (map fst -> args') <- mapM resolveExprValue args
       return_atom (LL.CallA f' args') rtypes'
     PrimCallE rtypes f args -> do
       rtypes' <- mapM resolveValueType rtypes
       (f', _) <- resolveExprValue f
       (map fst -> args') <- mapM resolveExprValue args
       return_atom (LL.PrimCallA f' args') rtypes'
     BinaryE op l r -> do
       (l', ltype) <- resolveExprValue l
       (r', rtype) <- resolveExprValue r
       let (bin_expr, bin_type, err) = mkBinary op l' ltype r' rtype
       lift $ throwErrorMaybe err
       return_atom bin_expr [bin_type]
     CastE e ty -> do
       (input_val, input_type) <- resolveExprValue e
       cast_type <- resolveValueType ty
       let (cast_expr, err) = mkCast input_type cast_type input_val
       lift $ throwErrorMaybe err
       return_atom cast_expr [cast_type]
     SizeofE ty -> do
       ty' <- resolveValueType ty
       return_value (nativeWordV $ sizeOf ty') (LL.PrimType nativeWordType)
     AlignofE ty -> do
       ty' <- resolveValueType ty
       return_value (nativeWordV (alignOf ty')) (LL.PrimType nativeWordType)
  where
    return_value val ty = return (Just val, LL.ValA [val], [ty])
    return_atom atom tys = return (Nothing, atom, tys)

resolveExprAtom :: Expr Parsed -> GenNR (LL.Atom, LL.ValueType)
resolveExprAtom e = do
  (_, atom, types) <- resolveExpr e
  case types of
    [ty] -> return (atom, ty)
    _ -> internalError "Expecting a single-valued expression"

-- | Resolve an expression and produce the results as values, along with the
-- type of each result value.
resolveExprValues :: Expr Parsed -> GenNR ([LL.Val], [LL.ValueType])
resolveExprValues e = do
  (mval, atom, types) <- resolveExpr e
  case mval of
    Just value -> return ([value], types)
    _ -> do values <- emitAtom types atom
            return (values, types)

-- | Resolve an expression and produce its result as a value.  It's an error 
-- for the expression to have zero or many results.
resolveExprValue :: Expr Parsed -> GenNR (LL.Val, LL.ValueType)
resolveExprValue e = do
  (mval, atom, types) <- resolveExpr e
  typ <- case types
         of [typ] -> return typ
            _ -> error "Expecting one return value from expression"
  case mval of
    Just value -> return (value, typ)
    Nothing -> do value <- emitAtom1 typ atom
                  return (value, typ)

resolveExprVar :: Expr Parsed -> GenNR LL.Var
resolveExprVar e = do
  (value, ty) <- resolveExprValue e
  tmpvar <- lift $ LL.newAnonymousVar ty
  bindAtom1 tmpvar (LL.ValA [value])
  return tmpvar

-- | Perform name resolution on an expression used to initialize static data.
-- Only literals, variables, and record constructions are allowed.
resolveStaticExpr :: Expr Parsed -> NR LL.Val
resolveStaticExpr expr =
  case expr
  of VarE vname -> do
       v <- lookupVar vname
       return $ LL.VarV v
     IntLitE ty n -> do
       ty' <- resolvePureValueType ty
       return $ LL.LitV $ mkIntLit ty' n
     FloatLitE ty n -> do
       ty' <- resolvePureValueType ty
       return $ LL.LitV $ mkFloatLit ty' n
     RecordE nm fields -> do
       record <- lookupRecord nm
       let record_type = resolvedRecordType record
       fields' <- mapM resolveStaticExpr fields
       return $ LL.RecV record_type fields'
     SizeofE ty -> do
       ty' <- resolvePureValueType ty
       return $ LL.LitV $ mkIntLit (LL.PrimType nativeWordType) (fromIntegral $ sizeOf ty')
     AlignofE ty -> do
       ty' <- resolvePureValueType ty
       return $ LL.LitV $ mkIntLit (LL.PrimType nativeWordType) (fromIntegral $ alignOf ty')
     _ -> error "Expression not permitted in initializer"

resolveAtom :: Atom Parsed -> GenNR (LL.Atom, [LL.ValueType])
resolveAtom (ValA [expr]) = do
  (_, atom, types) <- resolveExpr expr
  return (atom, types)

-- To resolve an expression list, generate values for the individual
-- expressions and then return a group of values
resolveAtom (ValA exprs) = do
  (unzip -> (vals, types)) <- mapM resolveExprValue exprs
  return (LL.ValA vals, types)

resolveAtom (IfA cond true false) = do
  -- Evaluate the condition
  (cond_val, _) <- resolveExprValue cond 
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

-- | Do name resolution on an lvalue.  The return value is a triple of the
-- variable that the rvalue gets bound to, generators for code that should
-- be executed after the binding, and bindings to add to the environment.
--
-- If the lvalue is a simple variable, then just translate and assign
-- the variable.  If it's a store expression, then assign to a temporary
-- variable, then store it.
resolveLValue lval ty =
  case lval
  of VarL var_name -> do
       v <- createVar Nothing var_name Nothing ty
       return (v, return (), defineVar v)
       
     StoreL base -> do
       v <- LL.newAnonymousVar ty
       return (v, store_value v base, return ())

     StoreFieldL base fld -> do
       v <- LL.newAnonymousVar ty
       return (v, store_field v base fld, return ())
     
     UnpackL rec lvals -> do
       v <- LL.newAnonymousVar ty
       
       -- Get the record field types
       record <- lookupRecord rec
       let record_type = resolvedRecordType record
       
       -- Type must match
       throwErrorMaybe $
         if ty == LL.RecordType record_type
         then Nothing
         else Just "Record unpack expression doesn't match type"

       -- Number of fields must match
       throwErrorMaybe $
         if length lvals == length (resolvedRecordFields record)
         then Nothing
         else Just "Record unpack expression has wrong number of fields"
       
       -- Bind each lvalue
       let lval_types = [ty | FieldDef ty _ <- resolvedRecordFields record]
       (unzip3 -> (lval_vars, lval_codes, lval_defs)) <-
         zipWithM_lazy resolveLValue lvals (map convertToValueType lval_types)
       
       -- Generate an 'unpack' atom
       let gen_code = bindAtom lval_vars (LL.UnpackA record_type (LL.VarV v))
       return (v, gen_code >> sequence_ lval_codes, sequence_ lval_defs)

     WildL -> do
       v <- LL.newAnonymousVar ty
       return (v, return (), return ())
  where
    -- Like zipWithM, but lazy in second list
    zipWithM_lazy f (x:xs) ~(y:ys) = liftM2 (:) (f x y) (zipWithM_lazy f xs ys)
    zipWithM_lazy f [] ~[] = return []

    store_value v base = do
      (base', _) <- resolveExprValue base
      primStore ty base' (LL.VarV v)

    store_field v base fld = do
      -- Compute the base and offset
      (base', _) <- resolveExprValue base
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
  createAndDefineVar nm Nothing ty'

resolveFunctionDef :: FunctionDef Parsed -> NR LL.FunDef
resolveFunctionDef fdef = do
  -- Define the function variable
  let function_type = if functionIsProcedure fdef
                      then LL.PrimType PointerType
                      else LL.PrimType OwnedType
  fvar <- createGlobalVar (functionName fdef) function_type

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

resolveDataDef ddef = do
  -- Get the defining expression
  value <- resolveStaticExpr $ dataValue ddef
  
  -- Initializer must be a record
  throwErrorMaybe $ must_be_record value

  -- Extract its fields (lazily)
  let LL.RecV record_type fields = value
  v <- createGlobalVar (dataName ddef) (LL.PrimType $ dataType ddef)
  return $ LL.DataDef v record_type fields
  where
    must_be_record (LL.RecV {}) = Nothing
    must_be_record _ = Just "Initializer must be a record value"

resolveDef :: Def Parsed -> NR ResolvedDef
resolveDef (FunctionDefEnt fdef) =
  fmap ResolvedFunctionDef $ resolveFunctionDef fdef

resolveDef (RecordDefEnt rdef) = do
  resolveRecordDef rdef
  return ResolvedRecordDef

resolveDef (DataDefEnt ddef) =
  fmap ResolvedDataDef $ resolveDataDef ddef

-- | Resolve a set of top-level definitions
resolveTopLevelDefs :: [Def Parsed] -> NR ([LL.FunDef], [LL.DataDef])
resolveTopLevelDefs defs = do
  -- Resolve global definitions
  rdefs <- mapM resolveDef defs
  return $ partitionResolvedDefinitions rdefs

-- | Resolve a set of external variable declarations.  The variables are 
-- added to the current scope.
withExternalVariables :: [ExternDecl Parsed] -> NR a -> NR ([LL.Var], a)
withExternalVariables edefs m = do
  evars <- mapM defineExternalVar edefs
  x <- with_evars evars m
  return (evars, x)
  where
    -- Save the external variables in the environment for later lookup
    with_evars evars m = NR $ \nrenv env errs ->
      let nrenv' = nrenv {externalVariables = evars ++ externalVariables nrenv}
      in runNR m nrenv' env errs

-- | Define an external variable
defineExternalVar (ExternDecl primtype lab mforeign_name) = do
  let name = labelUnqualifiedName lab
      mod = moduleOf lab
      ty = LL.PrimType primtype
  
  v <- createVar (Just mod) name mforeign_name ty
  
  -- If the variable is not in the current module, then define it.
  -- Otherwise, it will be defined later.
  current_module <- getSourceModuleName
  when (mod /= current_module) $ defineVar v

  return v

defineExternalVar (ImportDecl primtype local_name foreign_name) 
  | Just builtin_var <- getBuiltinByName foreign_name =
      -- Verify that the given name and type match
      if local_name /= foreign_name ||
         LL.varExternalName builtin_var /= Just foreign_name ||
         LL.varType builtin_var /= LL.PrimType primtype
      then error $ "Incompatible definition of built-in variable '" ++ local_name ++ "'"
      else do defineVar builtin_var
              return builtin_var
  | otherwise = do
      -- Create a variable imported from another language.  The variable
      -- resides in the 'builtin' module and has a foreign name.
      let ty = LL.PrimType primtype
      v <- createBuiltinVar local_name foreign_name ty
      defineVar v
      return v

generateLowLevelModule :: FilePath
                       -> ModuleName
                       -> [ExternDecl Parsed]
                       -> [Def Parsed]
                       -> IO LL.Module
generateLowLevelModule module_path module_name externs defs =
  withTheLLVarIdentSupply $ \var_ids -> do
    let ctx = NREnv var_ids [] module_name
        global_scope = []
        
        -- Start out in the global scope.
        -- Create the external variables, then process each top-level
        -- definition.
        generate_module = do
          (import_vars, (fun_defs, data_defs)) <-
            enterRec $ withExternalVariables externs $ resolveTopLevelDefs defs
          return $ LL.Module import_vars fun_defs data_defs

    (mod, _, errs) <- runNR generate_module ctx global_scope id

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

-- | Create a cast expression.  If there's no way to cast from the given input 
-- to the given output type, then produce an error
mkCast :: LL.ValueType          -- ^ Input type
       -> LL.ValueType          -- ^ Output type
       -> LL.Val                -- ^ Value to cast
       -> (LL.Atom, Maybe String) -- ^ Cast value and error message
mkCast (LL.PrimType input_type) (LL.PrimType output_type) input_val =
  case (input_type, output_type)
  of (OwnedType, OwnedType) -> success_id
     (OwnedType, PointerType) ->
       success $ LL.PrimA LL.PrimCastFromOwned [input_val]
     (PointerType, OwnedType) ->
       success $ LL.PrimA LL.PrimCastToOwned [input_val]
     (PointerType, PointerType) -> success_id
     _ -> cannot
  where
    success_id = success $ LL.ValA [input_val]
    success atom = (atom, Nothing)
    cannot = (internalError "mkCast", Just "Cannot generate type cast")

-- Cannot cast other types
mkCast (LL.RecordType _) _ _ =
  (internalError "mkCast", Just "Cannot cast from record type")

mkCast _ (LL.RecordType _) _ =
  (internalError "mkCast", Just "Cannot cast to record type")

-- | Create a binary expression.  If the expression is not well-typed, then
-- produce an error.
mkBinary :: BinOp -> LL.Val -> LL.ValueType -> LL.Val -> LL.ValueType
         -> (LL.Atom, LL.ValueType, Maybe String)
mkBinary op l_val l_type r_val r_type =
  case op
  of CmpEQOp -> comparison LL.CmpEQ
     AtomicAddOp -> atomic_int LL.PrimAAddZ
     _ -> internalError "mkBinary: Unhandled binary operator"
  where
    l_primtype = case l_type of ~(LL.PrimType pt) -> pt
    l_primtype_check =
      case l_type
      of LL.PrimType _ -> Nothing
         LL.RecordType _ -> Just "Operand may not have record type"
    r_primtype = case r_type of ~(LL.PrimType pt) -> pt
    r_primtype_check =
      case r_type
      of LL.PrimType _ -> Nothing
         LL.RecordType _ -> Just "Operand may not have record type"
         
    types_match_check =
      if l_primtype == r_primtype
      then Nothing
      else Just "Operands must have the same type"

    l_pointer_type_check = l_primtype_check `mappend`
      case l_primtype
      of PointerType -> Nothing
         _ -> Just "Operand must have pointer type"

    r_integral_type_check = r_primtype_check `mappend`
      case r_primtype
      of IntType {} -> Nothing
         _ -> Just "Operand must have integral type"

    comparison cmp_op =
      let operator =
            case l_primtype
            of IntType sgn sz -> LL.PrimCmpZ sgn sz cmp_op
               _ -> internalError "Binary comparison not implemented for this type"
          atom = LL.PrimA operator [l_val, r_val]
          checks = mconcat [l_primtype_check, r_primtype_check, types_match_check]
      in (atom, l_type, checks)
         
    atomic_int op =
      let operator =
            case r_primtype
            of IntType sgn sz -> op sgn sz
          atom = LL.PrimA operator [l_val, r_val]
          checks = mconcat [l_pointer_type_check, r_integral_type_check]
      in (atom, r_type, checks)