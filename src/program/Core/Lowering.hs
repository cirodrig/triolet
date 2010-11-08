{-| Lowering from core representation to low-level representation.
-}

{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, ViewPatterns #-}
module Core.Lowering(lower)
where

import Control.Monad
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.ST
import qualified Data.IntMap as IntMap
import Data.Maybe
import System.IO.Unsafe
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.Label
import Gluon.Common.Identifier
import Gluon.Common.MonadLogic
import Gluon.Common.Supply
import Gluon.Core
import Gluon.Eval.Environment
import Gluon.Eval.Equality
import Core.Syntax
import Core.Gluon
import Core.Print
import Core.BuiltinTypes
import Core.TypeLowering
import SystemF.Builtins
import qualified SystemF.Syntax as SystemF
import qualified LowLevel.Syntax as LL
import LowLevel.FreshVar
import qualified LowLevel.Label as LL
import LowLevel.Types
import LowLevel.Record
import LowLevel.Records
import LowLevel.Build
import LowLevel.Builtins
import qualified LowLevel.Print as LL
import Globals
import Export

-- | Convert a constructor to the corresponding value in the low-level IR.
--   Most constructors are translated to a global variable.  Pass-by-value 
--   constructors that take no parameters are translated to a value.
convertCon :: Con -> CvExp
convertCon c =
  case lowerBuiltinCoreFunction c
  of Just var -> value (CoreType $ conCoreReturnType c) (LL.VarV var)
     Nothing ->
       case IntMap.lookup (fromIdent $ conID c) convertConTable
       of Just retval ->
            -- Replaced by a hard-coded expression and type.
            retval
          Nothing -> internalError $
                     "convertCon: No translation for constructor " ++
                     showLabel (conName c)

-- | Conversions for constructors that translate to an expression rather than
-- a global variable in low-level code.
convertConTable = IntMap.fromList [(fromIdent $ conID c, v) | (c, v) <- tbl]
  where
    tbl = [] {- (pyonBuiltin the_passConv_int,
             value (LLType $ LL.RecordType passConvRecord) intPassConvValue)
          , (pyonBuiltin the_passConv_float,
             value (LLType $ LL.RecordType passConvRecord) floatPassConvValue)
          , (pyonBuiltin the_passConv_bool,
             value (LLType $ LL.RecordType passConvRecord) boolPassConvValue)
          , (pyonBuiltin the_additiveDict,
             atom [CoreType $ conCoreReturnType $ pyonBuiltin the_additiveDict]
             genAdditiveDictFun)
          ]-}

globalVarAssignment =
  IntMap.fromList [(fromIdent $ varID c, v) | (c, v) <- tbl]
  where
    tbl = [ (pyonBuiltin the_passConv_int_ptr,
             (LLType $ LL.PrimType PointerType, llBuiltin the_bivar_int_pass_conv))
          , (pyonBuiltin the_OpaqueTraversableDict_list_ptr,
             (LLType $ LL.PrimType PointerType, llBuiltin the_bivar_OpaqueTraversableDict_list))
          ]

isSingletonDataType c
  | c `elem` [pyonBuiltin the_AdditiveDict,
              pyonBuiltin the_TraversableDict,
              pyonBuiltin the_list,
              getPyonTupleType' 2] = True
  | c `elem` [] = False
  | otherwise =
      internalError $ 
      "isSingletonDataType: Not implemented for type: " ++ showLabel (conName c)

type BuildBlock a = Gen FreshVarM a

addressType = mkInternalConE (builtin the_Addr)

runFreshVar :: FreshVarM a -> Cvt a
runFreshVar m = Cvt $ ReaderT $ \env -> runFreshVarM (llVarSupply env) m

-- | A converted expression, together with its core type.
-- The core type determines what low-level representation to use 
-- for the data type.  It's not necessary to apply dependent type
-- parameters to compute the right type; consequently, variables
-- in the type expression are simply ignored.
data CvExp = Cv ![LoweringType] !CvExp'

expType :: CvExp -> [LoweringType]
expType (Cv t _) = t

data CvExp' =
    -- | A value
    CvVal !LL.Val

    -- | An expression.
    -- The expression is represented differently depending on
    -- whether it's in tail position.
  | CvExp !(BuildBlock LL.Atom)

-------------------------------------------------------------------------------
-- Monad for type conversion

newtype Cvt a = Cvt {runCvt :: ReaderT CvtEnv IO a} deriving(Monad, MonadIO)

data CvtEnv = CvtEnv { varSupply :: {-# UNPACK #-}!(IdentSupply Var)
                     , llVarSupply :: {-# UNPACK #-}!(IdentSupply LL.Var)
                       -- | Gluon type environment.  Only holds pure variables
                       --   that may appear in types.
                     , typeEnvironment :: [(Var, RExp)]
                       -- | Passing convention environment.  Only holds
                       --   parameter passing conventions and their types.
                     , passConvEnvironment :: [(AddrVar, PtrVar, RExp)]
                       -- | Variable assignments.  Holds the lowered equivalent
                       --   of all Core variables.
                     , varAssignment :: IntMap.IntMap (LoweringType, LL.Var)
                     }

instance Supplies Cvt (Ident Var) where
  fresh = Cvt $ ReaderT $ \env -> supplyValue $ varSupply env
  supplyToST f = Cvt $ ReaderT $ \env ->
    let get_fresh = unsafeIOToST $ supplyValue (varSupply env)
    in stToIO (f get_fresh)
  
instance Supplies Cvt (Ident LL.Var) where
  fresh = Cvt $ ReaderT $ \env -> supplyValue $ llVarSupply env

instance EvalMonad Cvt where
  liftEvaluation m = Cvt $ ReaderT $ \env -> do
    x <- runEvalIO (varSupply env) m
    case x of
      Nothing -> internalError "Cvt: evaluation failed"
      Just y -> return y

instance PureTypeMonad Cvt where
  assumePure v ty (Cvt m) = Cvt $ local add m
    where add env = env {typeEnvironment = (v, ty) : typeEnvironment env}

  getType v = Cvt $ asks $ lookup v . typeEnvironment
  
  peekType = getType
  
  getPureTypes = Cvt $ asks typeEnvironment
  
  liftPure m = Cvt $ ReaderT $ \env -> do
    result <- runPureTCIO (varSupply env) m
    case result of
      Left errs -> fail "Cvt: type errors occurred"
      Right x -> return x

  formatEnvironment f = Cvt $ ReaderT $ \env ->
    let msg = vcat [pprVar v <+> text ":" <+> pprExp t
                   | (v, t) <- typeEnvironment env]
    in runReaderT (runCvt (f msg)) env

doCvt :: IdentSupply Var -> IdentSupply LL.Var -> Cvt a -> IO a
doCvt var_supply anf_var_supply m = do
  let env = CvtEnv var_supply anf_var_supply [] [] globalVarAssignment
  runReaderT (runCvt m) env
      
lookupVar :: Var -> Cvt (LoweringType, LL.Var)
lookupVar v = Cvt $ asks $ \env ->
  case IntMap.lookup (fromIdent $ varID v) (varAssignment env)
  of Just x  -> x
     Nothing -> internalError "lookupVar: No assignment for variable"

-- | Record how to translate a variable to low-level code. 
convertVar :: Var -> LoweringType -> (LL.Var -> Cvt a) -> Cvt a
convertVar v ty k = do
  let label =
        case varName v
        of Just lab ->
             Just $ LL.pyonLabel (moduleOf lab) (labelUnqualifiedName lab)
           Nothing -> Nothing
  v' <- LL.newVar label (lowered ty)
  Cvt $ local (insert_binding v ty v') $ runCvt (k v')
  where
    -- Insert a mapping from core to ANF variable.
    -- Also insert a type assignment for this type variable.
    insert_binding v ty v' env =
      env { varAssignment = IntMap.insert (fromIdent $ varID v) (ty, v') $
                           varAssignment env}

assumeCoreVar :: Var -> RCType -> Cvt a -> Cvt a
assumeCoreVar v core_type m = do
  gluon_type <- coreToGluonType (verbatim core_type)
  assumePure v gluon_type m

-- | Add a parameter-passing convention dictionary to the environment.
-- The given type should be the dictionary's type parameter.
assumePassConvVar :: AddrVar -> PtrVar -> RCType -> Cvt a -> Cvt a
assumePassConvVar a p param_type m = do
  gluon_type <- coreToGluonType (verbatim param_type)
  Cvt $ local (insert_binding a p gluon_type) $ runCvt m
  where 
    insert_binding a p gluon_type env =
      env { passConvEnvironment = (a, p, gluon_type) : passConvEnvironment env}

-- | Get the parameter passing convention environment.
-- For each variable @v@of type @(PassConv t)@, include the pair @(v, t)@
-- in the returned list.
getPassConvEnvironment :: Cvt [(AddrVar, PtrVar, RExp)]
getPassConvEnvironment = Cvt $ asks passConvEnvironment

-------------------------------------------------------------------------------

type MkExp = Cvt CvExp

value :: LoweringType -> LL.Val -> CvExp
value ty v = Cv [ty] $ CvVal v

atom :: [LoweringType] -> BuildBlock LL.Atom -> CvExp
atom ty hd = Cv ty $ CvExp hd

asVal :: CvExp -> BuildBlock LL.Val
asVal (Cv ty x) =
  case x
  of CvVal val  -> return val
     CvExp hd -> asLet ty hd

toBlock :: [LoweringType] -> CvExp -> FreshVarM LL.Stm
toBlock return_types e =
  execBuild (map lowered return_types) $ do atom <- asAtom e
                                            return (LL.ReturnE atom)

asAtom :: CvExp -> BuildBlock LL.Atom
asAtom (Cv _ x) =
  case x
  of CvVal val -> return $ LL.ValA [val]
     CvExp hd -> hd

-- | Bind the single result of a piece of code to a variable.
asLet :: [LoweringType]           -- ^ Type of result
      -> BuildBlock LL.Atom       -- ^ Code whose result should be bound
      -> BuildBlock LL.Val        -- ^ Code with result bound to a variable
asLet [ty] hd = hd >>= emitAtom1 (lowered ty)

{-
-- | Generate code to compute the size of a data type
withSizeOf :: RCType -> Cvt (BuildBlock LL.Val)
withSizeOf ty = liftM get_size $ getPassConv ty
  where
    get_size pass_conv = do
      -- Get the passing convention
      pc_var <- pass_conv

      -- Get its 'size' field
      selectField passConvRecord 0 pc_var -}

-- | Return a description of a data type.  It may involve generating 
-- code to compute the data type description.
lowerToFieldType :: RCType -> Cvt (BuildBlock (), DynamicFieldType)
lowerToFieldType ty = 
  case unpackConAppCT ty
  of Just (con, args)
       | con `isPyonBuiltin` the_int -> return int_field
       | con `isPyonBuiltin` the_float -> return float_field
       | otherwise -> internalError "lowerToFieldType: No information for type"
     Nothing -> case ty
                of FunCT {} -> return owned_field
                   _ -> internalError "lowerToFieldType: Unexpected type"
  where
    int_field = (return (), PrimField pyonIntType)
    float_field = (return (), PrimField pyonFloatType)
    owned_field = (return (), PrimField OwnedType)

{-
-- | Generate code to compute the record layout of a data constructor with
--   the given type arguments.
recordLayoutOf :: Con -> [RCType] -> Cvt (BuildBlock DynamicRecord)
recordLayoutOf datacon type_args
  | datacon == getPyonTupleCon' 2 =
      liftM tupleRecordLayout $ mapM lowerToFieldType type_args

tupleRecordLayout size_and_alignments = do
  createDynamicRecord =<< sequence size_and_alignments 
  -}
-------------------------------------------------------------------------------
-- Parameter-passing conventions

-- | Look up a type's parameter passing convention value
lookupPassConv :: RCType -> Cvt (Maybe LL.Var)
lookupPassConv ty = do
  env <- getPassConvEnvironment
  
  -- Search for a matching variable in the environment 
  mcore_var <- liftPure $ do
    gluon_ty <- coreToGluonTypeWithoutEffects (verbatim ty)
    find_type (verbatim gluon_ty) env
    
  -- Get corresponding ANF variable
  case mcore_var of
    Nothing -> return Nothing
    Just (addr_var, ptr_var) -> do (_, v') <- lookupVar ptr_var
                                   return $ Just v'
  where
    find_type want_type ((addr_var, value_var, pc_type) : assocs) = do
      eq <- testEquality want_type (verbatim pc_type) 
      if eq
        then return (Just (addr_var, value_var))
        else find_type want_type assocs

    find_type _ [] = return Nothing

-- | Compute and return a parameter-passing convention variable
getPassConv :: RCType -> (LL.Val -> Cvt CvExp) -> Cvt CvExp
getPassConv ty k = do
  -- See if one is already available
  mpcvar <- lookupPassConv ty 
  case mpcvar of
    Just v  -> k (LL.VarV v)
    Nothing ->
      -- Try to construct a passing convention
      case unpackConAppCT ty
      of Just (con, args)
           | con `isPyonBuiltin` the_int ->
               k (builtinVar the_bivar_int_pass_conv)
           | con `isPyonBuiltin` the_float ->
               k (builtinVar the_bivar_float_pass_conv)
           | con `isPyonBuiltin` the_bool ->
               k (builtinVar the_bivar_bool_pass_conv)
           | con `isPyonBuiltin` the_PassConv ->
               k (builtinVar the_bivar_PassConv_pass_conv)
           | con `isPyonBuiltin` the_AdditiveDict ->
               k (builtinVar the_bivar_AdditiveDict_pass_conv)
           | con `isPyonBuiltin` the_TraversableDict ->
               k (builtinVar the_bivar_TraversableDict_pass_conv)
           | con `isPyonBuiltin` the_list ->
               case args
               of [arg] ->
                    getPassConv arg $ \arg_pc ->
                      build_unary_passconv
                      (llBuiltin the_fun_passConv_list)
                      arg_pc
         _ -> internalError $ "getPassConv: Unexpected type " ++ show (pprType ty)
  where
    build_unary_passconv pc_ctor arg_pc = do
      -- Create a variable that will point to the new term
      list_pc_ptr <- LL.newAnonymousVar (LL.PrimType PointerType)
      
      -- Create code using it
      code <- k (LL.VarV list_pc_ptr)
      
      -- Allocate local memory to hold the passconv variable
      let passconv_size = nativeWordV $ sizeOf passConvRecord
          code_type = map lowered $ expType code
          code' =
            allocateLocalMem list_pc_ptr passconv_size code_type $ do
              -- To create the passconv value, call the constructor function
              -- with type, passconv, and return pointer arguments
              emitAtom0 $ LL.CallA (LL.VarV pc_ctor) [ LL.LitV LL.UnitL
                                                     , arg_pc
                                                     , LL.VarV list_pc_ptr]
              
              -- Use it
              asAtom code
      return (Cv (expType code) (CvExp code'))

-------------------------------------------------------------------------------
-- Data structure lowering

-- | Load a field of a data structure.
--         
-- The returned function takes a pointer to the data structure as a
-- parameter, and returns a code generator that produces the loading code.
loadStructureField :: DataConField       -- ^ Field to load
                   -> CBind CParam Rec   -- ^ Parameter that binds the field
                   -> (LL.Var -> Cvt a)  -- ^ User of the parameter
                   -> Cvt (LL.Val -> BuildBlock (), a)
loadStructureField field (param ::: param_type) consumer =
  convertParameter (param ::: param_type) $ \llparam -> do
    consumer_rtn <- consumer llparam
    return (fetch_field llparam, consumer_rtn)
  where
    record_field = dataField field
    -- Fetch a field into a variable.  If it's a reference field,
    -- we may need to fetch a pointer or just get the offset.
    fetch_field llparam scrutinee_ptr =
      case param
      of ValP {} -> loadFieldAs record_field scrutinee_ptr llparam
         OwnP {} -> loadFieldAs record_field scrutinee_ptr llparam
         ReadP {} 
           | dataFieldIsReference field ->
               -- Load field, which contains pointer to the actual data
               loadFieldAs record_field scrutinee_ptr llparam
           | otherwise ->
               -- Get address of the field, which contains the actual data
               primAddPAs scrutinee_ptr (fieldOffset record_field) llparam

-- | Load multiple fields of a data structure.
--         
-- Each (field, parameter) pair loads the given field into the parameter
-- variable.  The field definition must agree with the parameter type.
loadStructureFields :: [(DataConField, CBind CParam Rec)]
                    -> ([LL.Var] -> Cvt a)
                    -> Cvt (LL.Val -> BuildBlock (), a)
loadStructureFields field_load_specs consumer = do
  (fetch_fields, x) <- lfs [] field_load_specs

  -- Combine all field-fetching code generators into one 
  let fetch_all_fields scrutinee_ptr = mapM_ ($ scrutinee_ptr) fetch_fields
  return (fetch_all_fields, x)
  where
    lfs loaded_values ((field, param) : fs) = do
      (fetch_field, (fetch_fields, x)) <-
        loadStructureField field param $ \llparam ->
        lfs (llparam : loaded_values) fs
      return (fetch_field : fetch_fields, x)
    
    lfs loaded_values [] = do
      x <- consumer (reverse loaded_values)
      return ([], x)

-- | Fetch the fields of a value, using the natural data representation of
-- the given data constructor instance.
unpackDataConstructorFields :: Con -- ^ Data constructor
                            -> [RCType] -- ^ Type parameters
                            -> [CBind CParam Rec] -- ^ Fields
                            -> ([LL.Var] -> Cvt a) -- ^ Code using the fields
                            -> Cvt (LL.Lit, LL.Val -> BuildBlock (), a)
unpackDataConstructorFields datacon ty_args params consumer = do
  -- Get layout information
  (tag, compute_record, constructor_layout) <-
    dataConstructorFieldLayout datacon ty_args
  unless (dataConLayoutNumFields constructor_layout == length params) $
    internalError "unpackDataConstructorFields: Wrong number of fields"
    
  -- Read fields and use the result
  (load_stuff, x) <-
    case constructor_layout
    of ReferenceLayout offset record_fields -> do
         (fetch_fields, x) <-
           loadStructureFields (zip record_fields params) consumer
  
         -- Combine layout computation with field reading
         let load_stuff scrutinee_ptr = do
               compute_record
               fetch_fields =<< primAddP scrutinee_ptr offset

         return (load_stuff, x)

       EnumValueLayout -> do x <- consumer []
                             return (\_ -> return (), x)

  return (tag, load_stuff, x)

-- | Data layout of a data constructor.
data DataConLayout =
    -- | This constructor is stored in memory, at some offset from the
    --   base pointer.  The offset and fields are given.
    ReferenceLayout !LL.Val ![DataConField]
    -- | This constructor is passed by value and has no fields.
  | EnumValueLayout

-- | How a field is stored in an object.
data DataConField =
  DataConField 
  { -- | The data representation in the object itself.  If the data is
    --   stored directly in the object, the field includes the entire
    --   data structure.  If it's a pointer to the data, this field is just
    --   a pointer.
    dataField :: !DynamicField
    -- | For pass-by-reference fields, this field is True if the field is
    --   a pointer to the real data, and false if the field is the real
    --   data.  For other represntations, this field is always false.
  , dataFieldIsReference :: !Bool
  }

inPlaceField, outOfPlaceField :: DynamicField -> DataConField
inPlaceField f = DataConField f False
outOfPlaceField f = DataConField f True

dataConLayoutNumFields :: DataConLayout -> Int
dataConLayoutNumFields (ReferenceLayout _ fs) = length fs
dataConLayoutNumFields EnumValueLayout = 0

-- | Get the layout of a data constructor field.
--
-- Returns the field tag, a code generator to compute the layout, and the
-- layout.
dataConstructorFieldLayout :: Con -> [RCType]
                           -> Cvt (LL.Lit, BuildBlock (), DataConLayout)
dataConstructorFieldLayout datacon ty_args
  | datacon `isPyonBuiltin` the_True = enum_value (LL.BoolL True)
  | datacon `isPyonBuiltin` the_False = enum_value (LL.BoolL False)
  | datacon == getPyonTupleCon' 2 = do
      (unzip -> (sequence_ -> computation1, field_layouts)) <-
        mapM lowerToFieldType ty_args
      
      (computation2, record_layout) <-
        suspendGen [] $ createDynamicRecord field_layouts
      
      let fields = map inPlaceField $ recordFields record_layout
      return (LL.UnitL,
              computation1 >> computation2,
              ReferenceLayout (nativeIntV 0) fields)

  | datacon `isPyonBuiltin` the_makeList =
      let fields =
            case recordFields $ toDynamicRecord listRecord
            of [size_fld, data_fld] ->
                 [inPlaceField size_fld, outOfPlaceField data_fld]
      in return (LL.UnitL,
                 return (),
                 ReferenceLayout (nativeIntV 0) fields)
  | datacon `isPyonBuiltin` the_additiveDict =
      -- This dictionary contains three functions
      let fields = map inPlaceField $ recordFields $
                   toDynamicRecord additiveDictRecord
      in return (LL.UnitL,
                 return (),
                 ReferenceLayout (nativeIntV 0) fields)
  
  | datacon `isPyonBuiltin` the_traversableDict =
      -- This dictionary contains two functions
      let fields = map inPlaceField $ recordFields $
                   toDynamicRecord traversableDictRecord
      in return (LL.UnitL,
                 return (),
                 ReferenceLayout (nativeIntV 0) fields)

  | otherwise = internalError $ "dataConstructorFieldLayout: Not implemented for " ++ showLabel (conName datacon)
  where
    enum_value tag = return (tag, return (), EnumValueLayout)

-------------------------------------------------------------------------------

-- | Add components of a value variable binding to the type environment.
--
--   Does not create a mapping to low-level variables.
bindValueVariable var core_type m = assumeCoreVar var core_type m

-- | Add components of a boxed variable binding to the environment.
--
--   Does not create a mapping to low-level variables.
--   Nothing is added to the environment.
bindBoxedVariable var core_type m = m

-- | Add components of a read reference variable binding to the environment.
--
--   Does not create a mapping to low-level variables.
bindReadVariable addr ptr core_type m =
  -- Add address variable to the environment.
  -- If this is a parameter-passing convention, record that.
  assumePure addr addressType $ assume_pass_conv m
  where
    assume_pass_conv m =
      case unpackConAppCT core_type
      of Just (con, args)
           | con `isPyonBuiltin` the_PassConv ->
             case args of [arg] -> assumePassConvVar addr ptr arg m
         _ -> m

loweredReturnType' (param ::: return_type) =
  loweredReturnType (returnType param ::: return_type)

-- Lower a return type.
-- Write-return functions don't return anything (they take an extra parameter
-- that they write into).
-- Other functions return a value.
loweredReturnType rbinder@(param ::: return_type) =
  case param
  of WriteRT -> []
     _ -> [CoreType rbinder]

convertExp :: RCExp -> Cvt CvExp
convertExp expression =
  case expression
  of ValCE {cexpVal = value} ->
       case value
       of ValueVarV v   -> lookup_var v
          OwnedVarV v   -> lookup_var v
          ReadVarV _ v  -> lookup_var v
          WriteVarV _ v -> lookup_var v
          ValueConV c   -> lookup_con c
          OwnedConV c   -> lookup_con c
          LitV lit      ->
            case lit
            of SystemF.IntL n   -> literal (LL.PrimType pyonIntType) $ 
                                   LL.IntL Signed pyonIntSize n
               SystemF.FloatL d -> literal (LL.PrimType pyonFloatType) $
                                   LL.FloatL pyonFloatSize d
               SystemF.BoolL b  -> literal (LL.PrimType pyonBoolType) $ LL.BoolL b
               SystemF.NoneL    -> literal (LL.PrimType pyonNoneType) LL.UnitL
          TypeV _       -> literal (LL.PrimType UnitType) LL.UnitL
     AppCE {cexpOper = op, cexpArgs = args, cexpReturnArg = rarg} ->
       convertApp op args rarg
     LamCE {cexpFun = f} -> do
       f' <- convertFun f
       return $ value (CoreType $ OwnRT ::: FunCT (cFunType f)) (LL.LamV f')
     LetCE {cexpBinder = binder, cexpRhs = rhs, cexpBody = body} ->
       convertLet binder rhs body
     LetrecCE {cexpDefs = defs, cexpBody = body} ->
       convertLetrec defs body
     CaseCE {cexpScrutinee = scr, cexpAlternatives = alts} ->
       convertCase scr alts
  where
    literal ty lit = return $ value (LLType ty) $ LL.LitV lit

    lookup_var v = do
      (ty, v') <- lookupVar v
      return $ value ty $ LL.VarV v'
    
    lookup_con c = return $ convertCon c

convertApp op args rarg = do
  -- Convert operator
  op' <- convertExp op
  let op_type = case expType op'
                of [t] -> t
                   _ -> internalError "convertApp"
      
  -- Convert operands
  args' <- mapM convertExp args

  -- Convert return operand
  args'' <-
    case rarg
    of Nothing -> return args'
       Just ra -> do ra' <- convertExp ra
                     return $ args' ++ [ra']
  
  -- Create application
  return_type <- applyFunctionType op_type args
  
  let atom_exp = do
        op'' <- asVal op' 
        args''' <- mapM asVal args''
        return $ LL.CallA op'' args'''
  
  return $ atom return_type atom_exp

-- | Compute the return type after applying a function to some number of 
-- parameters.
applyFunctionType :: LoweringType -> [RCExp] -> Cvt [LoweringType]
applyFunctionType _ [] = internalError "applyFunctionType"
applyFunctionType (LLType _) _ = internalError "applyFunctionType"
applyFunctionType (CoreType (OwnRT ::: op_type)) args =
  case op_type
  of FunCT ftype -> go_fresh (verbatim ftype) args
  where
    -- Freshen bound variables, then apply
    go_fresh fun_type args = do
      fun_type' <- freshenHead fun_type
      go fun_type' args
    
    -- Dependent application.  Substitute the argument value in the type.
    go (ArrCT {ctParam = ValPT (Just pvar) ::: _, ctRange = rng}) (arg:args) =
      let rng' =
            case arg
            of ValCE {cexpVal = value} ->
                 case value
                 of TypeV t     -> verbatim $ assignTypeFun pvar t rng
                    ValueVarV v -> assign pvar (mkInternalVarE v) rng
                    _ -> internalError "applyFunctionType: Unexpected parameter value"
      in go_fresh rng' args
    
    -- Non-dependent application.  Get the range.
    go (ArrCT {ctRange = rng}) (_:args) = go_fresh rng args
    
    -- Partial application
    go (ArrCT {ctParam = param, ctEffect = eff, ctRange = rng}) [] =
      let subst_type =
            ArrCT { ctParam = substituteCBind substituteCParamT substFully param
                  , ctEffect = substFully eff
                  , ctRange = substFully rng
                  }
      in return [CoreType (OwnRT ::: FunCT subst_type)]

    go (RetCT {ctReturn = ret}) [] =
      return $ loweredReturnType $
      substituteCBind substituteCReturnT substFully ret
    
    -- Excess arguments: this function should return a function.  Call the
    -- returned function with the remaining arguments.
    go (RetCT {ctReturn = ret}) args =
      case ret
      of OwnRT ::: ret_ty ->
           case substHead ret_ty
           of FunCT fun_ty -> go_fresh fun_ty args
              _ -> internalError "applyFunctionType: Too many arguments"
         _ -> internalError "applyFunctionType: Too many arguments"



convertLet binder@(bind_value ::: bind_type) rhs body =
  case bind_value
  of ValB v -> bind (bindValueVariable v bind_type) v
     OwnB v -> bind (bindBoxedVariable v bind_type) v
     LocalB a p -> bindReadVariable a p bind_type $ alloc p
     RefB _ v -> bind id v      -- Don't add anything to the environment
  where
    var_type = letBinderType binder
    
    -- Create a local memory area
    alloc p =
      -- Get the local data's parameter passing convention
      getPassConv bind_type $ \pass_conv_value ->
      
      -- The expression will bind a pointer
      convertVar p (CoreType var_type) $ \p' -> do
        rhs' <- convertExp rhs
        body' <- convertExp body

        -- The converted expression allocates memory, runs the RHS to 
        -- initialize the memory, and runs the body to use it.  The RHS
        -- doesn't return a value.
        let body_type = map lowered $ expType body'
        let make_expression =
              allocateLocalMem p' pass_conv_value body_type $ do
                -- Generate code.
                -- The RHS stores into memory; it returns nothing.
                asAtom rhs' >>= bindAtom0
                asAtom body'

        return $ atom (expType body') make_expression

    -- Bind to a temporary variable
    bind add_to_environment v = do
      rhs' <- convertExp rhs
      convertVar v (CoreType var_type) $ \v' -> add_to_environment $ do
        body' <- convertExp body
        
        let make_expression = do
              asAtom rhs' >>= bindAtom1 v'
              asAtom body'
              
        return $ atom (expType body') make_expression

convertLetrec defs body =
  convertDefGroup defs $ \defs' -> do
    body' <- convertExp body
    
    -- Insert a 'letrec' before the body
    let insert_letrec = do
          emitLetrec defs'
          asAtom body'
    return $ atom (expType body') insert_letrec

-- TODO: generalize this to arbitrary data types
convertCase scrutinee alternatives = do
  scr' <- convertExp scrutinee
  case expType scr' of
    [CoreType (ValRT ::: ty)] ->
      case unpackConAppCT ty
      of Just (con, args)
           | con `isPyonBuiltin` the_bool ->
               convertBoolCase scr' alternatives
           | otherwise -> unknown_constructor con
         _ -> invalid_type
    [CoreType (ReadRT _ ::: ty)] -> convertReferenceCase ty scr' alternatives
    _ -> invalid_type
    where
      invalid_type = internalError "convertCase: invalid scrutinee type"
      unknown_constructor con =
        internalError $ "convertCase: Don't know how to convert type: " ++ showLabel (conName con)
        
convertBoolCase scr alternatives = do
  (return_types, alts) <- convertAlternatives alternatives
  
  let make_expr = do
        scr_val <- asVal scr
        makeAlternativeBranch return_types scr_val scr_val alts
  return $ atom return_types make_expr

convertReferenceCase :: RCType -> CvExp -> [RCAlt] -> Cvt CvExp
convertReferenceCase ty scr alternatives =
  case unpackConAppCT ty
  of Just (con, args)
       | isSingletonDataType con ->
           case alternatives
           of [alt] -> do
                (_, alt_type, alt_exp) <- convertAlternative alt
                return $ atom alt_type (asVal scr >>= alt_exp)
       | otherwise -> do
           internalError "convertReferenceCase: Not implemented for this type"
     Nothing -> internalError "convertReferenceCase: Invalid type"

-- | Convert a case alternative.
--
--   Returns a code generator that builds the alternative, given the scrutinee.
--   The scrutinee is in the natural representation for its type: either a
--   value or a reference.
convertAlternative :: RCAlt
                   -> Cvt (LL.Lit,
                           [LoweringType],
                           LL.Val -> BuildBlock LL.Atom)
convertAlternative alt = do
  -- Add the parameter variables to the environment and determine how to get
  -- the constructor's fields
  let con = caltConstructor alt
  (tag, load_fields, body) <-
    unpackDataConstructorFields con (caltTyArgs alt) (caltParams alt) $ \_ ->
    convertExp $ caltBody alt
  
  -- In the case body, explicitly load the data structure fields 
  let alternative_exp scrutinee = load_fields scrutinee >> asAtom body

  return (tag, expType body, alternative_exp)

-- | Convert one or more case alternatives from the same case statement.  The
-- alternatives must have the same return type, which will be true if the input
-- was well-typed.
convertAlternatives alts = do
  xs <- mapM convertAlternative alts
  let return_type = case xs of (_, t, _):_ -> t
  return (return_type, [(tag, mk) | (tag, _, mk) <- xs])

-- | Assemble case alternatives into a @switch@ statement.
makeAlternativeBranch :: [LoweringType]
                      -> LL.Val
                      -> LL.Val
                      -> [(LL.Lit, LL.Val -> BuildBlock LL.Atom)]
                      -> BuildBlock LL.Atom
makeAlternativeBranch return_types scrutinee tag alts = do
  -- Create variables for each return value
  result_vars <- lift $ mapM LL.newAnonymousVar ll_return_types
  
  -- Create the case statement
  getContinuation False result_vars $ \cont -> do
    branches <- mapM (make_branch result_vars cont) alts
    return $ LL.SwitchE tag branches
  
  -- Return the return values
  return (LL.ValA $ map LL.VarV result_vars)
  where
    ll_return_types = map lowered return_types
    
    make_branch :: [LL.Var] -> LL.Stm -> (LL.Lit, LL.Val -> BuildBlock LL.Atom) -> BuildBlock (LL.Lit, LL.Stm)
    make_branch result_vars cont (tag, make_alternative) = do
      alternative <- lift $ execBuild ll_return_types $ do
        bindAtom result_vars =<< make_alternative scrutinee
        return cont
      return (tag, alternative)

convertFun = convertFunOrPrim LL.closureFun
convertPrim = convertFunOrPrim LL.primFun

convertFunOrPrim make_function fun =
  withMany convertParameter (cfunParams fun) $ \params ->
  convert_return (cfunReturn fun) $ \ret_param -> do
    let param_list = params ++ maybeToList ret_param
    let return_type = loweredReturnType' $ cfunReturn fun
    let ll_return_type = map lowered return_type
    body' <- convertExp $ cfunBody fun
    body_exp <- runFreshVar $ toBlock return_type body'
    return $ make_function param_list ll_return_type body_exp
  where
    -- Convert a write-return parameter to an actual pointer parameter
    convert_return (param ::: return_type) k =
      case param
      of ValR -> k Nothing
         OwnR -> k Nothing
         WriteR _ p -> convertVar p (LLType $ LL.PrimType PointerType) $ k . Just
         ReadR _ _ -> k Nothing

convertParameter (param ::: param_type) k =
  case param
  of ValP v ->
       bindValueVariable v param_type $
       convertVar v (CoreType $ ValRT ::: param_type) k
     OwnP v ->
       bindBoxedVariable v param_type $
       convertVar v (CoreType $ OwnRT ::: param_type) k
     ReadP a p ->
       let return_type = ReadRT (mkInternalVarE a) ::: param_type
       in bindReadVariable a p param_type $
          convertVar p (CoreType return_type) k

convertDefGroup :: [CDef Rec] -> ([LL.FunDef] -> Cvt a) -> Cvt a
convertDefGroup defgroup k = 
  -- First rename all functions
  withMany convert_function_name defgroup $ \fvars -> do
    -- Convert functions
    funs <- mapM convertFun [f | CDef _ f <- defgroup]
    
    -- Run continuation
    let defs = zipWith LL.FunDef fvars funs
    k defs
  where
    convert_function_name (CDef v f) k =
      convertVar v (CoreType $ OwnRT ::: FunCT (cFunType f)) k

-- | Wrap the lowered function 'f' in marshaling code for C.  Produce a
-- primitive function.
createCMarshallingFunction :: ExportSig -> LL.Fun -> Cvt LL.Fun
createCMarshallingFunction (ExportSig dom rng) f = do
  -- Generate marshaling code
  (unzip3 -> (concat -> dom_params, sequence_ -> marshal_params, dom_vals)) <-
    mapM marshalCParameter dom
  (rng_params, compute_rng, rng_vals, ret_vars) <- marshalCReturn rng

  -- Create the function
  fun_body <- runFreshVar $ execBuild (map LL.varType ret_vars) $ do
    marshal_params
    compute_rng (return $ LL.CallA (LL.LamV f) (dom_vals ++ rng_vals))
    return $ LL.ReturnE $ LL.ValA $ map LL.VarV ret_vars

  return $ LL.primFun dom_params (map LL.varType ret_vars) fun_body

marshalCParameter :: ExportDataType
                  -> Cvt ([LL.Var], BuildBlock (), LL.Val)
marshalCParameter ty =
  case ty
  of ListET _ -> pass_by_reference
     PyonIntET -> marshal_prim_type pyonIntType
     PyonFloatET -> marshal_prim_type pyonFloatType
     PyonBoolET -> marshal_prim_type pyonBoolType
  where
    -- Pass an object reference
    pass_by_reference = do
      v <- LL.newAnonymousVar (LL.PrimType PointerType)
      return ([v], return (), LL.VarV v)

    -- Pass a primitive type by value
    marshal_prim_type t = do
      v <- LL.newAnonymousVar (LL.PrimType t)
      return ([v], return (), LL.VarV v)

-- | Marshal a return value to C code.
--
-- Returns a list of parameters to the exported function,
-- a code generator that wraps the real function call,
-- a list of argument values to pass to the Pyon function, 
-- and a list of return variables to return from the wrapper function.
marshalCReturn :: ExportDataType
               -> Cvt ([LL.Var],
                       BuildBlock LL.Atom -> BuildBlock (),
                       [LL.Val],
                       [LL.Var])
marshalCReturn ty =
  case ty
  of ListET _ -> return_new_reference (LL.RecordType listRecord)
     PyonIntET -> marshal_prim_type pyonIntType
     PyonFloatET -> marshal_prim_type pyonFloatType
     PyonBoolET -> marshal_prim_type pyonBoolType     
  where
    -- Allocate and return a new object.  The allocated object is passed
    -- as a parameter to the function.
    return_new_reference t = do
      v <- LL.newAnonymousVar (LL.PrimType PointerType)
      
      let setup mk_real_call = do
            -- Allocate the return value
            allocateHeapMemAs (nativeWordV $ sizeOf t) v
            
            -- Call the function, which returns nothing
            emitAtom0 =<< mk_real_call

      return ([], setup, [LL.VarV v], [v])

    -- Just return a primitive value
    marshal_prim_type pt = do
      v <- LL.newAnonymousVar (LL.PrimType pt)
      
      let setup mk_real_call = bindAtom1 v =<< mk_real_call
          
      return ([], setup, [], [v])
      
convertExport module_name (CExport inf (ExportSpec lang exported_name) f) = do
  f' <- convertFun f
  fun_def <- case lang of CCall -> define_c_fun f'
  return (fun_def, (LL.funDefiniendum fun_def, export_sig))
  where
    export_sig = exportedFunctionSig $ cFunType f

    define_c_fun fun = do
      -- Generate marshalling code
      wrapped_fun <- createCMarshallingFunction export_sig fun

      -- Create function name.  Function is exported with the given name.
      let label = LL.externPyonLabel module_name exported_name (Just exported_name)
      v <- LL.newExternalVar label (LL.PrimType OwnedType)
      return $ LL.FunDef v wrapped_fun

convertModule (CModule module_name defss exports) = do 
  convertDefGroup (concat defss) $ \defs -> do
    (unzip -> (export_defs, exports_sigs)) <-
      mapM (convertExport module_name) exports
    return $ LL.Module { LL.moduleImports = allBuiltinImports
                       , LL.moduleFunctions = defs ++ export_defs
                       , LL.moduleData = []
                       , LL.moduleExports = exports_sigs
                       }

lower :: CModule Rec -> IO LL.Module
lower mod =
  withTheVarIdentSupply $ \var_supply ->
  withTheLLVarIdentSupply $ \anf_var_supply ->
  doCvt var_supply anf_var_supply $ convertModule mod