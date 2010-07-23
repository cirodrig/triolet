{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving #-}
module Pyon.Core.Lowering(lower)
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
import Pyon.Core.Syntax
import Pyon.Core.Gluon
import Pyon.Core.Print
import Pyon.Core.BuiltinTypes
import Pyon.SystemF.Builtins
import qualified Pyon.SystemF.Syntax as SystemF
import qualified Pyon.LowLevel.Syntax as LL
import Pyon.LowLevel.FreshVar
import Pyon.LowLevel.Types
import Pyon.LowLevel.Record
import Pyon.LowLevel.Build
import Pyon.LowLevel.Builtins
import Pyon.Globals

-- | Convert a constructor to the corresponding value in the low-level IR.
--   Most constructors are translated to a global variable.  Pass-by-value 
--   constructors that take no parameters are translated to a value.
convertCon :: Con -> (CvType, LL.Val)
convertCon c =
  case IntMap.lookup (fromIdent $ conID c) convertConTable
  of Just (Left var) ->
       -- Translated to a core variable.  Return the variable and the
       -- constructor's type.
       (Right $ conCoreReturnType c, LL.VarV var)
     Just (Right retval) ->
       -- Replaced by a hard-coded expression and type.
       retval
     Nothing -> internalError $
                "convertCon: No translation for constructor " ++
                showLabel (conName c)

convertConTable = IntMap.fromList [(fromIdent $ conID c, v) | (c, v) <- tbl]
  where
    tbl = [ (pyonBuiltin the_passConv_int,
             Right (Left $ LL.RecordType passConvRecord, intPassConvValue))
          , (pyonBuiltin Pyon.SystemF.Builtins.the_fun_store_int,
             Left $ llBuiltin Pyon.LowLevel.Builtins.the_fun_store_int)
          , (pyonBuiltin Pyon.SystemF.Builtins.the_fun_load_int,
             Left $ llBuiltin Pyon.LowLevel.Builtins.the_fun_load_int)
          , (pyonBuiltin (addMember . the_AdditiveDict_int),
             Left $ llBuiltin the_fun_add_int)
          ]

type BuildBlock a = Gen FreshVarM a

addressType = mkInternalConE (builtin the_Addr)

runFreshVar :: FreshVarM a -> Cvt a
runFreshVar m = Cvt $ ReaderT $ \env -> runFreshVarM (llVarSupply env) m

-- | A converted expression, together with its core type.
-- The core type determines what low-level representation to use 
-- for the data type.  It's not necessary to apply dependent type
-- parameters to compute the right type; consequently, variables
-- in the type expression are simply ignored.
data CvExp = Cv ![CvType] !CvExp'

expType :: CvExp -> [CvType]
expType (Cv t _) = t

-- | A converted type is either a value type or the un-converted core type.
--
-- At function calls, the core types of the function and any dependent
-- parameters are needed in order to compute the function's return type.
--
-- When a value is known not to be used dependently, or is inserted by the
-- translation, we can safely use the value type.  In general, we use the 
-- core type unless the value doesn't have a core type.
type CvType = Either LL.ValueType (CBind CReturnT Rec)

valueType :: CvType -> LL.ValueType
valueType (Left vt) = vt
valueType (Right (core_binder ::: core_type)) =
  case core_binder
  of ValRT ->
       case unpackConAppCT core_type
       of Just (con, args)
            | con `isPyonBuiltin` the_int -> LL.PrimType $ IntType Signed S32
            | con `isPyonBuiltin` the_float -> LL.PrimType $ FloatType S32
            | con `isPyonBuiltin` the_bool -> LL.PrimType BoolType
            | con `isPyonBuiltin` the_NoneType -> LL.PrimType UnitType
            | con `isPyonBuiltin` the_PassConv -> LL.RecordType passConvRecord
                 
          _ -> case core_type
               of ExpCT (LitE {expLit = KindL _}) -> LL.PrimType UnitType
                  _ ->internalError $ "valueType: Unexpected type " ++ show (pprType core_type)
     OwnRT -> LL.PrimType OwnedType
     WriteRT -> LL.PrimType PointerType
     ReadRT _ -> LL.PrimType PointerType
                   

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
                     , typeEnvironment :: [(Var, RExp)]
                     , varAssignment :: IntMap.IntMap (CvType, LL.Var)
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
  let env = CvtEnv var_supply anf_var_supply [] IntMap.empty
  runReaderT (runCvt m) env
      
lookupVar :: Var -> Cvt (CvType, LL.Var)
lookupVar v = Cvt $ asks $ \env ->
  case IntMap.lookup (fromIdent $ varID v) (varAssignment env)
  of Just x  -> x
     Nothing -> internalError "lookupVar: No assignment for variable"

convertVar :: Var -> CvType -> (LL.Var -> Cvt a) -> Cvt a
convertVar v ty k = do
  v' <- LL.newVar (varName v) (valueType ty)
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

-- | Get the parameter passing convention environment.
-- For each variable @v@of type @(PassConv t)@, include the pair @(v, t)@
-- in the returned list.
getPassConvEnvironment :: Cvt [(Var, RExp)]
getPassConvEnvironment = do
  types <- getPureTypes
  return $ mapMaybe pass_conv_types types
  where
    pass_conv_types (v, ty) =
      case ty
      of AppE {expOper = ConE {expCon = con}, expArgs = args}
           | con `isPyonBuiltin` the_PassConv ->
               case args
               of [arg] -> Just (v, arg) 
                  _ -> internalError "getPassConvEnvironment"
         _ -> Nothing

-------------------------------------------------------------------------------

type MkExp = Cvt CvExp

value :: CvType -> LL.Val -> CvExp
value ty v = Cv [ty] $ CvVal v

atom :: [CvType] -> BuildBlock LL.Atom -> CvExp
atom ty hd = Cv ty $ CvExp hd

asVal :: CvExp -> BuildBlock LL.Val
asVal (Cv ty x) =
  case x
  of CvVal val  -> return val
     CvExp hd -> asLet ty hd

toBlock :: CvExp -> FreshVarM LL.Block
toBlock e = execBuild $ asAtom e

asAtom :: CvExp -> BuildBlock LL.Atom
asAtom (Cv _ x) =
  case x
  of CvVal val -> return $ LL.ValA [val]
     CvExp hd -> hd

-- | Bind the single result of a piece of code to a variable.
asLet :: [CvType]                 -- ^ Type of result
      -> BuildBlock LL.Atom       -- ^ Code whose result should be bound
      -> BuildBlock LL.Val        -- ^ Code with result bound to a variable
asLet [ty] hd = hd >>= emitAtom1 (valueType ty)
  
-- | Generate code to compute the size of a data type
withSizeOf :: RCType -> Cvt (BuildBlock LL.Val)
withSizeOf ty = liftM get_size $ getPassConv ty
  where
    get_size pass_conv = do
      -- Get the passing convention
      pc_var <- pass_conv

      -- Get its 'size' field
      selectField passConvRecord 0 pc_var

-- | Generate code to compute the field information of a data type
fieldOf :: RCType -> Cvt (BuildBlock DynamicFieldType)
fieldOf ty = 
  case unpackConAppCT ty
  of Just (con, args)
       | con `isPyonBuiltin` the_int -> return int_field
       | con `isPyonBuiltin` the_float -> return float_field
       | otherwise -> internalError "fieldOf: No information for type"
     Nothing -> case ty
                of FunCT {} -> return owned_field
                   _ -> internalError "fieldOf: Unexpected type"
  where
    int_field = return $ toDynamicFieldType $ PrimField pyonIntType
    float_field = return $ toDynamicFieldType $ PrimField pyonFloatType
    owned_field = return $ toDynamicFieldType $ PrimField OwnedType

-- | Generate code to compute the record layout of a data constructor with
--   the given type arguments.
recordLayoutOf :: Con -> [RCType] -> Cvt (BuildBlock DynamicRecord)
recordLayoutOf datacon type_args
  | datacon == getPyonTupleCon' 2 =
      liftM tupleRecordLayout $ mapM fieldOf type_args

tupleRecordLayout size_and_alignments = do
  createDynamicRecord =<< sequence size_and_alignments 
  
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
    Just v  -> do (_, v') <- lookupVar v
                  return $ Just v'
  where
    find_type want_type ((var, pc_type) : assocs) = do
      eq <- testEquality want_type (verbatim pc_type) 
      if eq then return (Just var) else find_type want_type assocs

    find_type _ [] = return Nothing

-- | Compute and return a parameter-passing convention variable
getPassConv :: RCType -> Cvt (BuildBlock LL.Val)
getPassConv ty = do
  -- See if one is already available
  mpcvar <- lookupPassConv ty 
  case mpcvar of
    Just v  -> return (return $ LL.VarV v)
    Nothing ->
      -- Try to construct a passing convention
      case unpackConAppCT ty
      of Just (con, args)
           | con `isPyonBuiltin` the_int -> return (return intPassConvValue)
           | con `isPyonBuiltin` the_list -> undefined
         _ -> internalError $ "getPassConv: Unexpected type " ++ show (pprType ty)

-------------------------------------------------------------------------------

loweredReturnType' (param ::: return_type) =
  loweredReturnType (returnType param ::: return_type)

-- Lower a return type.
-- Write-return functions don't return anything (they take an extra parameter
-- that they write into).
-- Other functions return a value.
loweredReturnType rbinder@(param ::: return_type) =
  case param
  of WriteRT -> []
     _ -> [Right rbinder]

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
            of SystemF.IntL n   -> literal (Left (LL.PrimType $ IntType Signed S32)) $ 
                                   LL.IntL Signed S32 n
               SystemF.FloatL d -> literal (Left (LL.PrimType $ FloatType S32)) $
                                   LL.FloatL S32 d
               SystemF.BoolL b  -> literal (Left $ LL.PrimType BoolType) $ LL.BoolL b
               SystemF.NoneL    -> literal (Left $ LL.PrimType UnitType) LL.UnitL
          TypeV _       -> literal (Left $ LL.PrimType UnitType) LL.UnitL
     AppCE {cexpOper = op, cexpArgs = args, cexpReturnArg = rarg} ->
       convertApp op args rarg
     LamCE {cexpFun = f} -> do
       f' <- convertFun f
       return $ value (Right $ OwnRT ::: FunCT (cFunType f)) (LL.LamV f')
     LetCE {cexpBinder = binder, cexpRhs = rhs, cexpBody = body} ->
       convertLet binder rhs body
     LetrecCE {cexpDefs = defs, cexpBody = body} ->
       convertLetrec defs body
     CaseCE {cexpScrutinee = scr, cexpAlternatives = alts} ->
       convertCase scr alts
  where
    literal ty lit = return $ value ty $ LL.LitV lit

    lookup_var v = do
      (ty, v') <- lookupVar v
      return $ value ty $ LL.VarV v'
    
    lookup_con c =
      case convertCon c of (ty, val) -> return $ value ty val

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
  
  let atom_exp = liftM2 LL.CallA (asVal op') (mapM asVal args'')
  
  return $ atom return_type atom_exp

-- | Compute the return type after applying a function to some number of 
-- parameters.
applyFunctionType :: CvType -> [RCExp] -> Cvt [CvType]
applyFunctionType _ [] = internalError "applyFunctionType"
applyFunctionType (Left _) _ = internalError "applyFunctionType"
applyFunctionType (Right (_ ::: op_type)) args =
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
      in return [Right (OwnRT ::: FunCT subst_type)]

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
  of ValB v -> bind True v
     OwnB v -> bind False v
     LocalB a p -> assumePure a addressType $ alloc p
     RefB _ v -> bind False v
  where
    var_type = letBinderType binder
    
    -- Create a local memory area
    alloc p = do
      -- Get the local data's parameter passing convention
      pass_conv <- getPassConv bind_type
      
      -- The expression will bind a pointer
      convertVar p (Right var_type) $ \p' -> do
        rhs' <- convertExp rhs
        body' <- convertExp body

        -- The converted expression allocates memory, runs the RHS to 
        -- initialize the memory, and runs the body to use it.  The RHS
        -- doesn't return a value.
        let make_expression = do
              pass_conv_value <- pass_conv
              let body_type = map valueType $ expType body'
              allocateLocalObject p' pass_conv_value body_type $ do
                -- Generate code.
                -- The RHS stores into memory; it returns nothing.
                asAtom rhs' >>= bindAtom0
                asAtom body'

        return $ atom (expType body') make_expression

    -- Bind to a temporary variable
    bind add_to_environment v = do
      rhs' <- convertExp rhs
      convertVar v (Right var_type) $ \v' -> add_to_env $ do
        body' <- convertExp body
        
        let make_expression = do
              asAtom rhs' >>= bindAtom1 v'
              asAtom body'
              
        return $ atom (expType body') make_expression
      where
        -- Add the variable to the type environment
        add_to_env
          | add_to_environment = assumeCoreVar v bind_type
          | otherwise = id

convertLetrec defs body =
  convertDefGroup defs $ \defs' -> do
    body' <- convertExp body
    
    -- Insert a 'letrec' before the body
    let insert_letrec = do
          tell [LL.LetrecE defs']
          asAtom body'
    return $ atom (expType body') insert_letrec

-- TODO: generalize this to arbitrary data types
convertCase scrutinee alternatives = do
  scr' <- convertExp scrutinee
  case expType scr' of
    [Right (ValRT ::: ty)] ->
      case unpackConAppCT ty
      of Just (con, args)
           | con `isPyonBuiltin` the_bool ->
               convertBoolCase scr' alternatives
           | otherwise -> unknown_constructor con
         _ -> invalid_type
    [Right (ReadRT _ ::: ty)] ->
      case unpackConAppCT ty
      of Just (con, args)
           | con == getPyonTupleType' 2 ->
               convertTuple2Case scr' alternatives
           | otherwise -> unknown_constructor con
         _ -> invalid_type
    _ -> invalid_type
    where
      invalid_type = internalError "convertCase: invalid scrutinee type"
      unknown_constructor con =
        internalError $ "convertCase: Don't know how to convert type: " ++ showLabel (conName con)
        
convertBoolCase scr alternatives = do
  true_alt <- convertExp $ caltBody true_alternative
  false_alt <- convertExp $ caltBody false_alternative
  
  let make_expr = do
        scr_val <- asVal scr
        tr <- getBlock $ asAtom true_alt
        fa <- getBlock $ asAtom false_alt
        return (LL.SwitchA scr_val [(LL.BoolL True, tr), (LL.BoolL False, fa)])
  return $ atom (expType true_alt) make_expr
  where
    (true_alternative, false_alternative) =
      case alternatives
      of [alt1, alt2]
           | caltConstructor alt1 == pyonBuiltin the_True &&
             caltConstructor alt2 == pyonBuiltin the_False ->
               (alt1, alt2)
           | caltConstructor alt2 == pyonBuiltin the_True &&
             caltConstructor alt1 == pyonBuiltin the_False ->
               (alt2, alt1)
         _ -> internalError "convertBoolCase"

convertTuple2Case scr alternatives = do
  -- There's only one alternative, so we have no control flow to deal with
  (_, alt_type, alt_exp) <- convertRefAlternative alt
  let make_expr = asVal scr >>= alt_exp
  return $ atom alt_type make_expr
  where
    alt = case alternatives of [alt] -> alt
                               _ -> internalError "convertTuple2Case"

-- | Convert a case alternative, for a case statement that involves
-- a pass-by-reference data type.
convertRefAlternative :: RCAlt
                      -> Cvt (LL.Lit, [CvType], LL.Val -> BuildBlock LL.Atom)
convertRefAlternative alt = do
  -- Get the alternative's data layout
  layout <- recordLayoutOf (caltConstructor alt) (caltTyArgs alt)
  
  -- Add parameter variables to the environment
  withMany convertParameter (caltParams alt) $ \params -> do
    -- Convert the case body
    body <- convertExp $ caltBody alt
    
    -- In the case body, explicitly load the data structure fields 
    let alternative_exp scrutinee = do
          layout_data <- layout
          zipWithM_ (load_field scrutinee) (recordFields layout_data) params
          asAtom body
    return (LL.UnitL, expType body, alternative_exp)
  where
    load_field scrutinee fld param =
      loadFieldAs fld scrutinee param

convertFun fun =
  withMany convertParameter (cfunParams fun) $ \params ->
  convert_return (cfunReturn fun) $ \ret_param -> do
    let param_list = params ++ maybeToList ret_param
    let return_type = map valueType $ loweredReturnType' $ cfunReturn fun
    body' <- convertExp $ cfunBody fun
    body_exp <- runFreshVar $ toBlock body'
    return $ LL.closureFun param_list return_type body_exp
  where
    -- Convert a write-return parameter to an actual pointer parameter
    convert_return (param ::: return_type) k =
      case param
      of ValR -> k Nothing
         OwnR -> k Nothing
         WriteR _ p -> convertVar p (Left $ LL.PrimType PointerType) $ k . Just
         ReadR _ _ -> k Nothing

convertParameter (param ::: param_type) k =
  case param
  of ValP v ->
       convertVar v (Right $ ValRT ::: param_type) $ \v' ->
       assumeCoreVar v param_type (k v')
     OwnP v -> convertVar v (Right $ OwnRT ::: param_type) k
     ReadP a p ->
       let return_type = ReadRT (mkInternalVarE a) ::: param_type
       in assumePure a addressType $ convertVar p (Right return_type) k

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
      convertVar v (Right $ OwnRT ::: FunCT (cFunType f)) k

convertModule defss = do 
  convertDefGroup (concat defss) $ \defs ->
    return $ LL.Module { LL.moduleFunctions = defs
                       , LL.moduleData = []
                       }

lower :: [[CDef Rec]] -> IO LL.Module
lower defss =
  withTheVarIdentSupply $ \var_supply ->
  withTheLLVarIdentSupply $ \anf_var_supply ->
  doCvt var_supply anf_var_supply $ convertModule defss