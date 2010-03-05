
{-# LANGUAGE TypeFamilies, EmptyDataDecls, TypeSynonymInstances, UndecidableInstances, Rank2Types, NoMonomorphismRestriction #-}
module Pyon.NewCore.EffectInference where

import Control.Applicative(Const(..))
import Control.Monad
import Control.Monad.Fix
import qualified Data.Map as Map
import Data.Map(Map)
import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.SourcePos
import Gluon.Common.Supply
import Gluon.Core as Gluon
import Gluon.Core(Exp(..))
import qualified Gluon.Core.Builtins.Effect as Gluon.Builtins.Effect
import qualified  Gluon.Core.Builtins.Int as Gluon.Builtins.Int
import Gluon.Eval.Environment
import Gluon.Eval.Eval
import qualified Gluon.Eval.Typecheck as Gluon

import PythonInterface.Python
import Pyon.Globals
import Pyon.SystemF.Builtins
import Pyon.NewCore.Print
import Pyon.NewCore.Syntax
import Pyon.NewCore.Typecheck

foldM1 :: Monad m => (a -> a -> m a) -> [a] -> m a
foldM1 f (x:xs) = foldM f x xs
foldM1 _ [] = fail "foldM1: empty list"

withMany :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c
withMany f xs k = go xs k
  where
    go (x:xs) k = f x $ \y -> go xs $ \ys -> k (y:ys)
    go []     k = k []

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = liftM concat $ mapM f xs

-- | Get the effect type from a stream type expression.
-- Throw an error if the parameter isn't a stream type.
streamEffectType :: CWhnf -> CExp
streamEffectType exp =
  case unpackWhnfAppE exp
  of Just (con, [eff, _])
       | con `isPyonBuiltin` the_Stream -> eff
     _ -> internalError "Expecting a stream type"

-- | Get the result type from a stream type expression.
-- Throw an error if the parameter isn't a stream type.
streamResultType :: CWhnf -> CExp
streamResultType exp =
  case unpackWhnfAppE exp
  of Just (con, [_, rt])
       | con `isPyonBuiltin` the_Stream -> rt
     _ -> internalError "Expecting a stream type"

type EffectType = CWhnf

data PackedReadList =
  PackedReadList
  { listAddr :: !Var            -- ^ Address of list
  , listPtr  :: !Var            -- ^ Pointer to list
  , listType :: !(Exp Core)     -- ^ Type of list element
  }
data UnpackedReadList =
  UnpackedReadList
  { listPackedList :: !PackedReadList
  , listSize :: !Var            -- ^ Number of elements in list 
  , listDataAddr :: !Var        -- ^ Address of list data array
  , listDataPtr  :: !Var        -- ^ Pointer to list data array
  }

-- | A data type expanded into its components
data DataElaboration =
    IsPackedReadList {-# UNPACK #-} !PackedReadList
  | IsUnpackedReadList {-# UNPACK #-} !UnpackedReadList

type DataElaborationMap = Map Var DataElaboration

emptyEffect :: EffectType
emptyEffect = Whnf Gluon.Builtins.Effect.empty

-- Compute the union of two effects, after checking for the common case where
-- one of the effects is empty.
effectUnion :: EffectType -> EffectType -> LinTC EffectType
effectUnion e1 e2 =
  ifEmpty e1 (return e2) $
  ifEmpty e2 (return e1) $
  let effectUnion = Gluon.Builtins.Effect.sconj (whnfExp e1) (whnfExp e2)
  in liftM renameWhnfExpFully $ evalHead' effectUnion
  where
    ifEmpty e ifTrue ifFalse =
      case unpackWhnfAppE e1
      of Just (con, args) | con `isBuiltin` the_EmpS -> ifTrue
         _ -> ifFalse

-- | Effect inference updates an unpacked data map.
-- The effect inference maintains a completed elaboration map and an
-- in-progress elaboration map.
newtype EffInf a =
  EffInf {runEffInf :: DataElaborationMap
                    -> DataElaborationMap
                    -> LinTC (DataElaborationMap, a)}

instance Supplies EffInf VarID where
  fresh = liftEvaluation fresh

instance Monad EffInf where
  return x = EffInf $ \eager_m lazy_m -> return (eager_m, x)
  m >>= k = EffInf $ \eager_m lazy_m -> do 
    (eager_m', x) <- runEffInf m eager_m lazy_m
    runEffInf (k x) eager_m' lazy_m

instance EvalMonad EffInf where
  liftEvaluation m = liftLin $ liftEvaluation m
    
instance PureTypeMonad EffInf where
  assumePure v e m = EffInf $ \eager_m lazy_m -> 
    assumePure v e $ runEffInf m eager_m lazy_m
  getType v = liftPure $ getType v
  peekType v = liftPure $ peekType v
  getType' pos v = liftPure $ getType' pos v
  peekType' pos v = liftPure $ peekType' pos v
  getPureTypes = liftPure getPureTypes
  liftPure m = liftLin $ liftPure m

instance LinearTypeMonad EffInf where
  assume v e = applyLinTCTransformation (assume v e)
  assumeLinear v e = applyLinTCTransformation (assumeLinear v e)

liftLin :: LinTC a -> EffInf a
liftLin m = EffInf $ \eager_m _ -> do
  x <- m
  return (eager_m, x)
  
applyLinTCTransformation :: (forall a. LinTC a -> LinTC a) 
                         -> (forall b. EffInf b -> EffInf b)
applyLinTCTransformation t m = EffInf $ \eager_m lazy_m ->
  t $ runEffInf m eager_m lazy_m

runEffectInference :: EffInf a -> LinTC a
runEffectInference m = do
  (_, x) <- mfix $ \ ~(lazy_m, _) -> runEffInf m Map.empty lazy_m
  return x

-------------------------------------------------------------------------------

createPackedReadList :: EvalMonad m => Type Core -> m PackedReadList
createPackedReadList element_type = do
  addr_var <- newTemporary ObjectLevel Nothing
  ptr_var <- newTemporary ObjectLevel Nothing
  return $ PackedReadList 
           { listAddr = addr_var
           , listPtr = ptr_var
           , listType = element_type
           }

createUnpackedReadList :: EvalMonad m => PackedReadList -> m UnpackedReadList
createUnpackedReadList prl = do
  size_var <- newTemporary ObjectLevel Nothing
  dat_addr_var <- newTemporary ObjectLevel Nothing
  dat_ptr_var <- newTemporary ObjectLevel Nothing
  return $ UnpackedReadList
    { listPackedList = prl
    , listSize = size_var
    , listDataAddr = dat_addr_var
    , listDataPtr = dat_ptr_var
    }

-- | Given a list variable and its element type, get the list's elaboration as
-- an unpacked, readable list
listModeUnpackedRead :: Var -> Type Core -> EffInf UnpackedReadList
listModeUnpackedRead v ty = EffInf $ \eager_m lazy_m -> do
  updated_eager_m <- update_map eager_m
  return ( updated_eager_m
         , lookup_result lazy_m)
  where
    -- Look up the UnpackedReadList information
    lookup_result lazy_m =
      case Map.lookup v lazy_m
      of Just (IsUnpackedReadList x) -> x
         _ -> internalError "listModeUnpackedRead: wrong mode"
    
    -- Ensure there is an UnpackedReadList in the map
    update_map eager_m =
      case Map.lookup v eager_m
      of Nothing -> do 
           x <- createPackedReadList ty
           y <- createUnpackedReadList x
           return $ Map.insert v (IsUnpackedReadList y) eager_m
         Just (IsPackedReadList x) -> do
           y <- createUnpackedReadList x
           return $ Map.insert v (IsUnpackedReadList y) eager_m
         Just (IsUnpackedReadList _) -> do
           return eager_m
  
-- | Given a list variable and its element type, get the list's elaboration as
-- an packed, readable list
listModePackedRead :: Var -> Type Core -> EffInf PackedReadList
listModePackedRead v ty = EffInf $ \eager_m lazy_m -> do
  updated_eager_m <- update_map eager_m
  return ( updated_eager_m
         , lookup_result lazy_m)
  where
    -- Look up the PackedReadList information
    lookup_result lazy_m =
      case Map.lookup v lazy_m
      of Just (IsUnpackedReadList x) -> listPackedList x
         Just (IsPackedReadList x) -> x
         _ -> internalError "listModePackedRead: wrong mode"
    
    -- Insert a PackedReadList if not present
    update_map eager_m =
      case Map.lookup v eager_m
      of Nothing -> do
           x <- createPackedReadList ty
           return $ Map.insert v (IsPackedReadList x) eager_m
         Just (IsPackedReadList {}) -> return eager_m
         Just (IsUnpackedReadList {}) -> return eager_m

{-
data EffectInference

type EIExp = Exp EffectInference
type EITuple = Tuple EffectInference
type EISum = Sum EffectInference
type EIVal = Val EffectInference 
type EIStm = Stm EffectInference

instance Syntax EffectInference where
  type ExpOf EffectInference = Const (EffInf (Typed (RecExp Core)))
  type TupleOf EffectInference = TupleOf Core
  type SumOf EffectInference = SumOf Core
  {-
  injectExp = mapExp injectExp injectTuple injectSum . snd
  injectTuple = mapTuple injectExp injectTuple
  injectSum = mapSum injectExp injectSum
  substExp _ = unsafeCoerce (substExp (undefined :: Core))
  substTuple _ = unsafeCoerce (substTuple (undefined :: Core))
  substSum _ = unsafeCoerce (substSum (undefined :: Core))
  -}

instance PyonSyntax EffectInference where
  type ValOf EffectInference = Const (EffInf (Typed (Val Core)))
  type StmOf EffectInference = Const (EffInf (Typed (Stm Core)))

runExpType :: RecExp EffectInference -> EffInf (Typed (RecExp Core))
runExpType = getConst

runExp :: RecExp EffectInference -> EffInf (RecExp Core)
runExp x = do (_, stm) <- getConst x
              return stm

runStmType :: RecStm EffectInference -> EffInf (Typed (RecStm Core))
runStmType = getConst
    
runStm :: RecStm EffectInference -> EffInf (RecStm Core)
runStm x = do (_, stm) <- getConst x
              return stm
    
runValType :: RecVal EffectInference -> EffInf (Typed (RecVal Core))
runValType  x = getConst x

runVal :: RecVal EffectInference -> EffInf (RecVal Core)
runVal x = do (_, stm) <- getConst x
              return stm

effectInference :: PyonWorker EffectInference
effectInference = PyonWorker gluonWorker
                             (\v ty -> Const (effectInferVal v ty)) 
                             (\v ty eff -> Const (effectInferStm v ty eff))
  where
    gluonWorker :: Gluon.TCWorker EffectInference
    gluonWorker = Gluon.tcWorker doExp doTuple doSum kindE
    doExp e ty = Const (effectInferExp e ty)
    doTuple t = t
    doSum s   = s
    kindE     = Const (return ((internalError "No type for 'kind'"),
                               Gluon.LitE (internalSynInfo SortLevel) Gluon.SortL))
-}

checkEscapingVar :: Var -> CExp -> EffInf ()
checkEscapingVar var type_expr =
  when (type_expr `mentions` var) $ fail $ "Local variable escapes" ++ show var

checkEscapingVars :: [Var] -> CExp -> EffInf ()
checkEscapingVars vars type_expr =
  when (type_expr `mentionsAny` vars) $ fail $ "Local variable escapes"  ++ show vars

-------------------------------------------------------------------------------
-- Effect inference routines

-- | Rewrite a call expression and return the new expression.  
--
-- First, the function is checked against some special builtin method names. 
-- If a match is found, the call is rewritten.
-- Otherwise, the function arguments are rewritten.
-- This may cause an update to the data elaboration map.
rewriteCall :: SynInfo
            -> TypeAnn Val Core   -- ^ Function
            -> [TypeAnn Val Core] -- ^ Arguments
            -> CWhnf              -- ^ Return type of original call
            -> EffInf (TypeAnn Val Core) -- ^ New call
rewriteCall info oper args return_type = do
  new_val <-
    case typeAnnValue oper
    of GluonV {valGluonTerm = expression} ->
         case expression
         of ConE {expCon = c}
              | c `isPyonBuiltin` traverseMember . the_TraversableDict_list ->
                rewriteListTraversal info (map typeAnnValue args) return_type
              | c `isPyonBuiltin` the_oper_CAT_MAP ->
                rewriteCatMap info args
            _ -> rewriteArguments
       _ -> rewriteArguments
  return new_val
  where
    rewriteArguments = do
      args' <- concatMapM (rewriteArgument info) args
      return $ TypeAnn return_type $ AppV info (typeAnnValue oper) args'

-- Rewrite the "concatMap" operation.  Compute the new effect type.
rewriteCatMap info [effect_type, first_return_type, second_return_type,
                    second_stream, first_stream] = do
  let pos = getSourcePos info

  -- Get the effect type out of each stream's type
  let first_eff = streamEffectType $ typeAnnotation first_stream
  second_stream_type <-
    case whnfExp $ typeAnnotation second_stream
    of FunE {expRange = r} -> liftM renameWhnfExpFully $ evalHead' r
  let second_eff = streamEffectType second_stream_type
  
  -- Compute the union of their types
  let new_eff_type = Gluon.Builtins.Effect.sconj first_eff second_eff    
  
  -- Create the type of the resulting stream
  let new_result_type = mkInternalWhnfAppE (pyonBuiltin the_Stream)
                        [new_eff_type, streamResultType second_stream_type]
  
  let new_exp =
        AppV info (mkConV pos $ pyonBuiltin the_oper_CAT_MAP)
        [ expToVal new_eff_type
        , typeAnnValue first_return_type
        , typeAnnValue second_return_type
        , typeAnnValue second_stream
        , typeAnnValue first_stream
        ]

  -- Use this as the new effect type.  Other parameters are unchanged.
  return $ TypeAnn new_result_type new_exp

-- Rewrite a function argument.
-- List parameters are rewritten to (address, value) pairs
rewriteArgument info arg =
  case unpackWhnfAppE $ typeAnnotation arg
  of Just (con, [elt_type])
       | con `isPyonBuiltin` the_list -> do
           list_variable <-
             case typeAnnValue arg
             of GluonV {valGluonTerm = VarE {expVar = v}} -> return v 
                _ -> internalError "Cannot handle unknown list parameter" 

           -- Look up packed list info
           packed_read_fields <- listModePackedRead list_variable elt_type
           return [ mkVarV (getSourcePos info) $ listAddr packed_read_fields
                  , mkVarV (getSourcePos info) $ listPtr packed_read_fields
                  ]
     _ -> return [typeAnnValue arg]

-- rewrite (traverse ls) to 
-- (generate ls_size (\i -> do loadListElement ls_element_type 
--                                             ls_data_addr 
--                                             ls_data_ptr
--                                             i))
rewriteListTraversal info [elt_type, list_value] old_return_type = do
  list_variable <- 
    case list_value
    of GluonV {valGluonTerm = VarE {expVar = v}} -> return v
       _ -> internalError "Cannot handle traversal of an unknown list"
  
  -- We must be reading the list contents here
  unpacked_read_fields <- listModeUnpackedRead list_variable (valToExp elt_type)

  -- New temporary variable for the load index
  index_var <- newTemporary ObjectLevel Nothing

  -- Construct the rewritten expression
  let pos = getSourcePos info
      dat_addr = mkVarE pos $ listDataAddr unpacked_read_fields
      dat_ptr = mkVarE pos $ listDataPtr unpacked_read_fields
      dat_size = mkVarE pos $ listSize unpacked_read_fields
      elt_type' = valToExp elt_type
      load_call = mkConAppE pos (pyonBuiltin the_loadListElement)
                  [elt_type', dat_addr, dat_ptr, mkVarE pos index_var]
      -- effect_type := listElementEffect dat_addr (Stored elt_type) index
      effect_type = mkInternalConAppE (pyonBuiltin the_listElementEffect)
                    [ dat_addr
                    , mkInternalConAppE (pyonBuiltin the_Stored) [elt_type']
                    , mkVarE noSourcePos index_var
                    ]
      -- load_return_type := Stream effect_type element_type
      load_return_type = mkInternalWhnfAppE (pyonBuiltin the_Stream)
                         [effect_type, elt_type']
      load_fun :: StreamFun Core
      load_fun = Fun [Binder index_var Gluon.Builtins.Int.intType ()]
                     (whnfExp load_return_type)
                     Gluon.Builtins.Effect.empty -- Effect type is ignored
                     (GluonV info load_call)
      -- total_effect_type := listContentsEffect dat_addr (Stored elt_type) size
      total_effect_type = 
        mkInternalConAppE (pyonBuiltin the_listContentsEffect)
        [ dat_addr
        , mkInternalConAppE (pyonBuiltin the_Stored) [elt_type']
        , dat_size
        ]
      traverse_expr = AppV info (mkConV pos (pyonBuiltin the_generate))
                      [ expToVal total_effect_type
                      , elt_type
                      , expToVal dat_size
                      , SLamV info load_fun
                      ]
  return $ TypeAnn load_return_type traverse_expr

-- Cannot rewrite if we got the wrong number of arguments
rewriteListTraversal _ _ _ =
  internalError "Undersaturated application of list traversal function"

-- | Effect inference on an expression.  If it's a call expression, try to
-- rewrite it.  Leave other expressions alone.
effectInferExp :: RecExp (Typed Core) -> EffInf (TypeAnn Exp Core)
effectInferExp expression =
  case typeAnnValue expression
  of AppE {expInfo = inf, expOper = op, expArgs = args} -> do
       op' <- effectInferExp op
       args' <- mapM effectInferExp args
       let return_type = typeAnnotation expression
       call' <- rewriteCall inf (asValue op') (map asValue args') return_type
       return $ mapTypeAnn valToExp call'
     _ -> traverseTypeAnn (traverseExp runExp runTuple runSum) expression
  where
    asValue :: TypeAnn Exp Core -> TypeAnn Val Core
    asValue (TypeAnn ty exp) = TypeAnn ty (expToVal exp)
    
    runExp e = liftM typeAnnValue $ effectInferExp e
    runTuple = traverseTuple runExp runTuple
    runSum = traverseSum runExp runSum

effectInferVal :: RecVal (Typed Core) -> EffInf (TypeAnn Val Core)
effectInferVal value =
  case typeAnnValue value
  of GluonV {valGluonTerm = exp} -> do
       exp' <- effectInferExp exp
       return $ mapTypeAnn expToVal exp'
     AppV {valInfo = inf, valOper = op, valArgs = args} -> do
       op' <- effectInferVal op
       args' <- mapM effectInferVal args
       rewriteCall inf op' args' (typeAnnotation value)
     ALamV {valInfo = inf, valAFun = fun} -> do
       (ty', fun') <- effectInferActionFun fun
       return $ TypeAnn ty' (ALamV inf fun')
     SLamV {valInfo = inf, valSFun = fun} -> do
       (ty', fun') <- effectInferStreamFun fun
       return $ TypeAnn ty' (SLamV inf fun')
     SDoV {valInfo = inf, valStm = stm} -> do
       EffAnn ty eff stm' <- effectInferStm stm
       
       -- Create a stream type
       let stream_type = mkInternalWhnfAppE (pyonBuiltin the_Stream) 
                         [whnfExp eff, whnfExp ty]
       return $ TypeAnn stream_type (SDoV inf stm')

effectInferStm :: RecStm (Typed Core)
               -> EffInf (EffAnn Stm Core)
effectInferStm statement = 
  case effAnnValue statement
  of ReturnS {stmInfo = inf, stmVal = val} -> do
       TypeAnn ty val' <- effectInferVal val
       return $ EffAnn ty emptyEffect (ReturnS inf val')
     CallS {stmInfo = inf, stmVal = val} -> do
       TypeAnn call_type val' <- effectInferVal val
       case unpackWhnfAppE call_type of
         Just (con, [eff_ty, ret_ty])
           | con `isPyonBuiltin` the_Action -> do
               eff_ty' <- liftM renameWhnfExpFully $ evalHead' eff_ty
               ret_ty' <- liftM renameWhnfExpFully $ evalHead' ret_ty
               return $ EffAnn ret_ty' eff_ty'  (CallS inf val')
         _ -> internalError "Call does not have Action type"
     LetS {stmInfo = inf, stmVar = lhs, stmStm = rhs, stmBody = body} -> do
       rhs' <- effectInferStm rhs
       body' <- assumeMaybe lhs (whnfExp $ returnAnnotation rhs') $ do
         body' <- effectInferStm body
         
         -- Local variable must not be mentioned in return type or effect
         case lhs of
           Nothing -> return ()
           Just v  -> do
             checkEscapingVar v $ whnfExp (returnAnnotation body')
             checkEscapingVar v $ whnfExp (effectAnnotation body')
         return body'
         
       -- Combine effect types
       eff_ty <- liftLin $
                 effectUnion (effectAnnotation rhs') (effectAnnotation body')
       
       let ret_ty = returnAnnotation body'
       return $ EffAnn ret_ty eff_ty (LetS inf lhs (effAnnValue rhs') (effAnnValue body'))
     LetrecS {stmInfo = inf, stmDefs = defs, stmBody = body} -> do
       assumeDefs defs $ \defs' -> do
         body' <- effectInferStm body
         return $ mapEffAnn (LetrecS inf defs') body'
     CaseS {stmInfo = inf, stmScrutinee = val, stmAlts = alts} -> do 
       val' <- effectInferVal val
       alts' <- sequence $ map (effectInferAlt (typeAnnotation val')) alts
       let alt_type = returnAnnotation $ head alts'
           alt_statements = map effAnnValue alts'
       eff <- liftLin $ foldM1 effectUnion $ map effectAnnotation alts'
       return $ EffAnn alt_type eff (CaseS inf (typeAnnValue val') alt_statements)
  where
    assumeMaybe Nothing _ k  = k
    assumeMaybe (Just x) t k = assumePure x t k

    
assumeDefs :: [Def (Typed Core)] 
           -> ([Def Core] -> EffInf a) 
           -> EffInf a
assumeDefs defs k = withMany assumeDef defs k
  where
    assumeDef (Def info var meaning) k = do
      meaning' <- 
        case meaning
        of ActionFunDef f -> do
             (_, f') <- effectInferActionFun f
             return $ ActionFunDef f'
           StreamFunDef f -> do
             (_, f') <- effectInferStreamFun f
             return $ StreamFunDef f'
      k $ Def info var meaning'

effectInferAlt :: CWhnf -> Alt (Typed Core) -> EffInf (EffAnn Alt Core)
effectInferAlt scrutinee_type (Alt inf pat body) =
  applyLinTCTransformation (matchPattern scrutinee_type pat) $ do
    EffAnn rt et body' <- effectInferStm body
    let pat_vars = patternVars pat
    checkEscapingVars pat_vars (whnfExp rt)
    checkEscapingVars pat_vars (whnfExp et)
    return $ EffAnn rt et (Alt inf pat body')

assumeParams params k = withMany assumeParam params k
  where
    assumeParam (Binder v ty ()) k = do
      TypeAnn _ ty' <- effectInferExp ty 
      assume v ty' $ k (Binder v ty' ())

paramVars binders = map binderVar binders
  where
    binderVar (Binder v _ ()) = v

patternVars (ConP _ fields) = mapMaybe fieldVar fields
  where
    fieldVar RigidP = Nothing
    fieldVar (FlexibleP v) = Just v

actionFunctionType :: [Binder Core ()] -> Type Core -> Type Core -> Whnf Core
actionFunctionType params ret eff =
  let range = Gluon.mkInternalWhnfAppE (pyonBuiltin the_Action) [ret, eff]
  in functionType params range

functionType :: [Binder Core ()] -> Whnf Core -> Whnf Core
functionType params (Whnf range) = Whnf $ foldr mkFun range params
  where
    mkFun (Binder v ty ()) range
      | range `mentions` v = mkInternalFunE False v ty range
      | otherwise          = mkInternalArrowE False ty range

effectInferActionFun :: ActionFun (Typed Core) 
                     -> EffInf (CWhnf, ActionFun Core)
effectInferActionFun fun =
  assumeParams (funParams fun) $ \params -> do
    -- Ignore the function's annotated return and effect types
    TypeAnn _ _ <- effectInferExp $ funReturnType fun
    TypeAnn _ _ <- effectInferExp $ funEffectType fun
    EffAnn return_type effect_type body <- effectInferStm $ funBody fun
    
    -- Return and effect types must not mention parameters
    let param_vars = paramVars params
        return_type_exp = whnfExp return_type
        effect_type_exp = whnfExp effect_type
    checkEscapingVars param_vars return_type_exp
    checkEscapingVars param_vars effect_type_exp
    
    let function_type = actionFunctionType params return_type_exp effect_type_exp
    return (function_type, Fun params return_type_exp effect_type_exp body)

effectInferStreamFun :: StreamFun (Typed Core) 
                     -> EffInf (CWhnf, StreamFun Core)
effectInferStreamFun fun =
  assumeParams (funParams fun) $ \params -> do
    rt <- liftM renameWhnfExpFully . evalHead' . typeAnnValue =<<
          effectInferExp (funReturnType fun)
    TypeAnn return_type body <- effectInferVal $ funBody fun
    
    -- Return type must not mention parameters
    let param_vars = paramVars params
    checkEscapingVars param_vars (whnfExp return_type)
    
    let function_type = functionType params return_type
        function_exp = Fun params (whnfExp return_type) (whnfExp emptyEffect) body
    return (function_type, function_exp)

effectInferModule :: Module Core -> IO (Module Core)
effectInferModule mod = do
  result <- withTheVarIdentSupply $ \supply ->
    runLinTCIO supply $ do
      Module defs <- leaveLinearScope $ typeScanModule saveType mod
      liftM Module (runEffectInference $ assumeDefs defs $ return)
  case result of
    Left errs -> do mapM_ (putStrLn . showTypeCheckError) errs
                    throwPythonExc pyRuntimeError "Type checking failed"
    Right mod -> return mod
