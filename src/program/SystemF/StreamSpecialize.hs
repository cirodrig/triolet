{-| After optimizations at the System F level to get rid of superfluous
-- class dictionaries, we specialize all appearances of the Traversable 
-- class into stream-traversing and data-structure-traversing cases.
-- After specialization, streams are no longer a member of the Traversable 
-- class.  Effect inference requires this.
-}

{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, ViewPatterns #-}
module SystemF.StreamSpecialize(doSpecialization)
where

import Control.Monad
import Control.Monad.Reader
import Data.List
import Data.Maybe
import qualified Data.IntMap as IntMap
import Debug.Trace

import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.SourcePos
import Gluon.Common.Supply
import Gluon.Core.Level
import Gluon.Core(internalSynInfo)

import Globals
import Builtins.Builtins
import SystemF.Print
import SystemF.Syntax
import Type.Var
import Type.Type

withMany :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c
withMany f xs k = go xs k
  where
    go (x:xs) k = f x $ \y -> go xs $ \ys -> k (y:ys)
    go []     k = k []

-- | A specialization table is stored as a trie.  At each level, inspect one
-- type parameter and take a branch.
data SpclTable =
    Don'tCare !SpclTable
    -- ^ Specialize (is stream) (is not stream)
  | Specialize !SpclTable !SpclTable
    -- | The specialized variable
  | End !Var
    -- | This variable was a stream dictionary, and was eliminated by 
    -- specialization
  | EliminatedDict

showSpclTable :: SpclTable -> Doc
showSpclTable (Don'tCare x) =
  hang (text "Don'tCare") 2 $ showSpclTable x
showSpclTable (Specialize l r) =
  hang (text "Specialize") 2 $ showSpclTable l $$ showSpclTable r
showSpclTable (End v) = text "End"
showSpclTable EliminatedDict = text "Eliminated"

-- | Properties of a type that are important to specialization.
data SpclType =
    Don'tCareType                 -- ^ Doesn't particpate in specialization
  | IsStreamType                  -- ^ Is a stream
  | NotStreamType                 -- ^ Is not a stream
    deriving(Eq, Show)

-- | If the type is a traversable dictionary type, return the type parameter,
-- which must be a type variable.  Otherwise, return Nothing.
traversableDictTypeParameter :: RType -> Maybe Var
traversableDictTypeParameter (SFType ty) =
      case fromVarApp ty
      of Just (c, args)
           | c `isPyonBuiltin` the_TraversableDict ->
               -- Argument must be a type variable
               case args
               of [VarT v] -> Just v
                  _ -> internalError "traversableDictTypeParameter: Unexpected traversable dictionary type"
         _ -> Nothing
  
traversableDictTypeParameter _ = internalError "traversableDictTypeParameter"

-- | Information about whether a type is a stream.
-- The stream type is a stream; all other types are not.
globalTypeTable :: IntMap.IntMap SpclType
globalTypeTable =
  IntMap.fromList [(fromIdent $ varID v, is_stream v)
                  | v <- pureV : allBuiltinVars, getLevel v /= ObjectLevel]
  where
    is_stream v
      | v `isPyonBuiltin` the_Stream = IsStreamType
      | otherwise = NotStreamType

-- | Information about how to specialize built-in functions and constructors.
globalConTable :: IntMap.IntMap SpclTable
globalConTable =
  IntMap.fromList [(fromIdent $ varID $ pyonBuiltin c, tbl)
                  | (c, tbl) <- assocs]
  where
    -- Create an entry that is not specialized.  The 'arity' is the number of 
    -- type parameters the entry takes.
    unchanged arity field =
      (field, don't_cares arity $ pyonBuiltin field)
      where
        don't_cares n x = iterate Don'tCare (End x) !! n

    assocs =
      [ unchanged 0 the_repr_int
      , unchanged 0 the_repr_float
      , unchanged 0 the_repr_bool
      , unchanged 0 the_repr_NoneType
      , unchanged 1 the_repr_iter
      , unchanged 1 the_repr_list
      , unchanged 0 the_repr_Any
      , unchanged 1 the_repr_owned
      , unchanged 0 the_makeComplex
      , unchanged 0 (const $ pyonTupleReprCon 0)
      , unchanged 1 (const $ pyonTupleReprCon 1)
      , unchanged 2 (const $ pyonTupleReprCon 2)
      , unchanged 0 (const $ pyonTupleCon 0)
      , unchanged 1 (const $ pyonTupleCon 1)
      , unchanged 2 (const $ pyonTupleCon 2)
      , unchanged 1 the_eqDict
      , unchanged 1 the_ordDict
      , unchanged 1 the_traversableDict
      , unchanged 1 the_additiveDict
      , unchanged 1 the_multiplicativeDict
      , unchanged 0 the_EqDict_int_eq
      , unchanged 0 the_EqDict_int_ne
      , unchanged 0 the_EqDict_float_eq
      , unchanged 0 the_EqDict_float_ne
      , unchanged 2 the_EqDict_Tuple2_eq
      , unchanged 2 the_EqDict_Tuple2_ne
      , unchanged 0 the_OrdDict_int_le
      , unchanged 0 the_OrdDict_int_lt
      , unchanged 0 the_OrdDict_int_ge
      , unchanged 0 the_OrdDict_int_gt
      , unchanged 0 the_OrdDict_float_le
      , unchanged 0 the_OrdDict_float_lt
      , unchanged 0 the_OrdDict_float_ge
      , unchanged 0 the_OrdDict_float_gt
      , unchanged 0 the_OrdDict_Tuple2_le
      , unchanged 0 the_OrdDict_Tuple2_lt
      , unchanged 0 the_OrdDict_Tuple2_ge
      , unchanged 0 the_OrdDict_Tuple2_gt
      , unchanged 0 the_AdditiveDict_int_add
      , unchanged 0 the_AdditiveDict_int_sub
      , unchanged 0 the_AdditiveDict_int_negate
      , unchanged 0 the_AdditiveDict_int_zero
      , unchanged 0 the_AdditiveDict_float_add
      , unchanged 0 the_AdditiveDict_float_sub
      , unchanged 0 the_AdditiveDict_float_negate
      , unchanged 0 the_AdditiveDict_float_zero
      , unchanged 0 the_MultiplicativeDict_int_mul
      , unchanged 0 the_MultiplicativeDict_int_fromInt
      , unchanged 0 the_MultiplicativeDict_int_one
      , unchanged 0 the_MultiplicativeDict_float_mul
      , unchanged 0 the_MultiplicativeDict_float_fromInt
      , unchanged 0 the_MultiplicativeDict_float_one
      , unchanged 1 the_TraversableDict_Stream_traverse
      , unchanged 1 the_TraversableDict_Stream_build
      , unchanged 1 the_TraversableDict_list_traverse
      , unchanged 1 the_TraversableDict_list_build
      , unchanged 1 the_oper_DIV
      , unchanged 0 the_oper_MOD
      , unchanged 1 the_oper_POWER
      , unchanged 1 the_oper_FLOORDIV
      , unchanged 0 the_oper_BITWISEAND
      , unchanged 0 the_oper_BITWISEOR
      , unchanged 0 the_oper_BITWISEXOR
      , unchanged 2 the_oper_CAT_MAP
      , unchanged 1 the_oper_DO
      , unchanged 1 the_fun_undefined
      , unchanged 0 the_fun_iota
      , unchanged 1 the_additiveDict_complex
      , unchanged 1 the_add_complex
      , unchanged 1 the_sub_complex
      , unchanged 1 the_negate_complex
      , unchanged 1 the_zero_complex
      , (the_fun_map,
         Specialize
         (Don'tCare $ Don'tCare $ End $ pyonBuiltin the_fun_map_Stream)
         (Don'tCare $ Don'tCare $ End $ pyonBuiltin the_fun_map))
      , (the_fun_reduce,
         Specialize
         (Don'tCare $ End $ pyonBuiltin the_fun_reduce_Stream)
         (Don'tCare $ End $ pyonBuiltin the_fun_reduce))
      , (the_fun_reduce1,
         Specialize
         (Don'tCare $ End $ pyonBuiltin the_fun_reduce1_Stream) 
         (Don'tCare $ End $ pyonBuiltin the_fun_reduce1))
      , (the_fun_zip,
         Specialize
         (Specialize
          (Don'tCare $ Don'tCare $ End $ pyonBuiltin the_fun_zip_SS)
          (Don'tCare $ Don'tCare $ End $ pyonBuiltin the_fun_zip_SN))
         (Specialize
          (Don'tCare $ Don'tCare $ End $ pyonBuiltin the_fun_zip_NS)
          (Don'tCare $ Don'tCare $ End $ pyonBuiltin the_fun_zip)))
      ]

-- | Create a specialization table for a value that isn't specialized.
-- The table has one don't-care parameter for each type parameter.
unchangedType :: RType -> Var -> SpclTable
unchangedType (SFType ty) x = add_don't_cares ty (End x)
  where
    add_don't_cares ty x =
      case ty
      of FunT (_ ::: dom) (_ ::: ty2)
           | getLevel dom == KindLevel -> Don'tCare $ add_don't_cares ty2 x
         _ -> x

-------------------------------------------------------------------------------

newtype Spcl a = Spcl (ReaderT SpclEnv IO a) deriving(Monad, Functor)

runSpcl :: IdentSupply Var -> Spcl a -> IO a
runSpcl supply (Spcl m) =
  let env = SpclEnv supply globalTypeTable globalConTable
  in runReaderT m env

data SpclEnv =
  SpclEnv
  { spclEnvVarIDs :: !(IdentSupply Var)
  , spclEnvTypes :: IntMap.IntMap SpclType
  , spclEnvTable :: IntMap.IntMap SpclTable
  }

instance Supplies Spcl (Ident Var) where
  fresh = Spcl $ ReaderT $ \env -> supplyValue $ spclEnvVarIDs env

spclLocal :: (SpclEnv -> SpclEnv) -> Spcl a -> Spcl a
spclLocal t (Spcl m) = Spcl (local t m)

spclAsks :: (SpclEnv -> a) -> Spcl a
spclAsks f = Spcl (asks f)

assumeType :: Var -> SpclType -> Spcl a -> Spcl a
assumeType v ty m = spclLocal add_entry m
  where
    add_entry env =
      env {spclEnvTypes = IntMap.insert (fromIdent $ varID v) ty $
                          spclEnvTypes env}

assumeTypeMaybe :: Maybe Var -> SpclType -> Spcl a -> Spcl a
assumeTypeMaybe Nothing  ty m = m
assumeTypeMaybe (Just v) ty m = assumeType v ty m

lookupType :: Var -> Spcl SpclType
lookupType v = spclAsks $ \env ->
  case IntMap.lookup (fromIdent $ varID v) $ spclEnvTypes env
  of Nothing -> internalError $ "lookupType: No information for type variable " ++ show v
     Just x  -> x

assumeVarSpclTable :: Var -> SpclTable -> Spcl a -> Spcl a
assumeVarSpclTable v tbl m = spclLocal add_entry m
  where
    add_entry env =
      env {spclEnvTable =
              IntMap.insert (fromIdent $ varID v) tbl $ spclEnvTable env}

lookupVarSpclTable :: Var -> Spcl SpclTable
lookupVarSpclTable v = spclAsks $ \env ->
  case IntMap.lookup (fromIdent $ varID v) $ spclEnvTable env
  of Nothing -> internalError $ "lookupVarSpclTable: No information for variable " ++ show v
     Just x  -> x

-- | Specialize a type.  Type variables that have been specialized to 'Stream'
-- in the current context are replaced with 'Stream'.
--
-- N.B. We assume the type is not stream-polymorphic.
specializeType :: RType -> Spcl RType
specializeType (SFType ty) = fmap SFType $ specializeType' ty

specializeType' ty =
  case ty
  of VarT v -> do
       spcl_type <- lookupType v
       case spcl_type of
         IsStreamType -> return $ VarT (pyonBuiltin the_Stream)
         _            -> return ty
     AppT op arg -> liftM2 AppT (specializeType' op) (specializeType' arg)
     FunT (ValPT mparam ::: dom) (ret ::: rng) -> do
       dom' <- specializeType' dom

       -- Assume the parameter is not specialized
       rng' <- assumeTypeMaybe mparam Don'tCareType $ specializeType' rng
       return $ FunT (ValPT mparam ::: dom') (ret ::: rng')

-- | Use the given type to select one entry from a specialization table.    
--   The table determines what decision has to be made.  If a specialization 
--   decision is to be made, then decide whether the given type is a 'Stream'
--   type.
pickSpecialization :: SpclTable -> RType -> Spcl (Bool, SpclTable)
pickSpecialization tbl ty =
  case tbl
  of Don'tCare x    -> return (True, x)
     Specialize l r -> do
       spcl_type <-
         case fromVarApp $ fromSFType ty
         of Just (v, _) -> lookupType v
            _ -> return NotStreamType
       pick_one spcl_type l r
     _ -> wrong
  where
    pick_one IsStreamType  l _ = return (False, l)
    pick_one NotStreamType _ r = return (True, r)
    pick_one Don'tCareType _ _ = wrong
    wrong = internalError "pickSpecialization"

pickFullSpecialization :: SpclTable -> [RType] -> Spcl (Maybe ([Bool], Var))
pickFullSpecialization tbl tys = pick [] tbl tys
  where
    pick tl tbl (ty:tys) = do
      (keep_param, tbl') <- pickSpecialization tbl ty
      pick (keep_param:tl) tbl' tys
      
    pick tl tbl [] = case finishSpecialization tbl
                     of Just x  -> return $ Just (tl, x)
                        Nothing -> return Nothing

    -- Given a partly or fully applied function, generate the
    -- specialized value.  Fail if not enough parameters were given to
    -- choose the specialized value.
    finishSpecialization (End x) = Just x
    finishSpecialization EliminatedDict = Nothing
    finishSpecialization (Don'tCare x) = finishSpecialization x
    finishSpecialization _ = internalError "finishSpecialization"


-- | Specialize a pattern.  If the pattern is removed by specialization, then 
-- Nothing is returned.
specializePat :: RPat -> Spcl (Maybe RPat)
specializePat (VarP v ty) = 
  case traversableDictTypeParameter ty
  of Nothing -> specialize_and_return
     Just tv -> do
       -- Check whether this dictionary pattern is removed
       spcl_type <- lookupType tv
       case spcl_type of
         IsStreamType -> return Nothing
         NotStreamType -> specialize_and_return
         Don'tCareType -> internalError "specializePat"
  where
    specialize_and_return = do
       ty' <- specializeType ty
       return $ Just $ VarP v ty'
       
specializePat _ = internalError "specializePat: Not a variable pattern"

-- | Assume a pattern-bound variable.  The variable is monomorphic and 
-- will not be specialized.
assumePat :: RPat -> Spcl a -> Spcl a
assumePat (VarP v t) m = assumeVarSpclTable v (unchangedType t v) m

assumePats :: [RPat] -> Spcl a -> Spcl a
assumePats ps m = foldr assumePat m ps

specializeAndAssumePat :: RPat -> (Maybe RPat -> Spcl a) -> Spcl a
specializeAndAssumePat pat@(VarP v ty) k = do
  mpat' <- specializePat pat
  case mpat' of
    Nothing   -> assumeVarSpclTable v EliminatedDict $ k mpat'
    Just pat' -> assumePat pat' $ k mpat'

specializeAndAssumePats :: [RPat] -> ([RPat] -> Spcl a) -> Spcl a
specializeAndAssumePats ps k =
  withMany specializeAndAssumePat ps (k . catMaybes)

-- | Specialize an expression.
specialize :: RExp -> Spcl RExp
specialize expression = do
  e' <- specializeMaybe expression
  case e' of
    Nothing -> internalError "specialize: Not expecting a dictionary value here"
    Just e  -> return e

specializeMaybe :: RExp -> Spcl (Maybe RExp)
specializeMaybe expression =
  case expression
  of VarE {} -> specializeTyAppExpNonCall expression
     LitE {} -> return $ Just expression -- Literals are never specialized
     TyAppE {} -> specializeTyAppExpNonCall expression
     CallE {expInfo = inf, expOper = op, expArgs = args} -> 
       specializeCall inf op args
     FunE {expInfo = inf, expFun = f} -> do
       f' <- specializeFun f
       return $ Just $ FunE {expInfo = inf, expFun = f'}
     LetE {expInfo = inf, expBinder = b, expValue = rhs, expBody = body} -> do
       rhs' <- specialize rhs

       -- The local variable is never a dictionary, so it's never eliminated
       Just b' <- specializePat b
       body' <- assumePat b' $ specialize body
       return $ Just $ LetE { expInfo = inf
                            , expBinder = b'
                            , expValue = rhs'
                            , expBody = body'}
     LetrecE {expInfo = inf, expDefs = defs, expBody = body} -> do
       (defs', body') <- specializeDefs defs $ specialize body
       return $ Just $ LetrecE { expInfo = inf
                               , expDefs = defs'
                               , expBody = body'}
     CaseE {expInfo = inf, expScrutinee = scr, expAlternatives = alts} -> do
       mscr' <- specializeMaybe scr
       case mscr' of
         Just scr' -> do
           alts' <- mapM specializeAlt alts
           return $ Just $ CaseE { expInfo = inf
                                 , expScrutinee = scr
                                 , expAlternatives = alts'}
         Nothing ->
           -- Deconstructing a traversable object dictionary.  Replace the
           -- pattern variables with stream-specific members.
           case alts
           of [alt] -> specializeDictionaryAlternative alt
              
-- | If the expression constructs a new Traversable dictionary, return the
-- dictionary type parameter.
-- 
-- Match the expression against the pattern
-- @TyAppE {expOper = "traversableDict", expArgs = [t]}@
matchTraversableDictCall :: RExp -> Spcl (Maybe RType)
matchTraversableDictCall expression =
  case expression
  of TyAppE {expOper = op, expTyArg = arg_ty} 
       | is_the_constructor op -> fmap Just $ specializeType arg_ty
     _ -> return Nothing
  where
    is_the_constructor op =
      case op
      of VarE {expVar = c} -> c `isPyonBuiltin` the_traversableDict
         _      -> False

specializeDictionaryAlternative (Alt { altTyArgs = [_]
                                     , altParams = [VarP traverse_var _,
                                                    VarP build_var _]
                                     , altBody = body
                                     }) =
  let body' = substituteTraversableMethods traverse_var build_var body
  in specializeMaybe body'

-- | Replace any occurences of dictionary methods with the Gluon constructors
-- for stream build and traverse methods.
substituteTraversableMethods traverse_var build_var expr = go expr
  where
    go expr =
      case expr
      of VarE {expInfo = inf, expVar = v}
           | v == traverse_var ->
             VarE {expInfo = inf, 
                   expVar = pyonBuiltin the_TraversableDict_Stream_traverse}
           | v == build_var ->
             VarE {expInfo = inf,
                   expVar = pyonBuiltin the_TraversableDict_Stream_build}
           | otherwise -> expr
         LitE {} -> expr
         TyAppE inf op arg -> TyAppE inf (go op) arg
         CallE inf op args -> CallE inf (go op) (map go args)
         FunE inf f -> FunE inf $ dofun f
         LetE inf b rhs body -> LetE inf b (go rhs) (go body)
         LetrecE inf defs b ->
           LetrecE inf [Def v (dofun f) | Def v f <- defs] (go b)
         CaseE inf scr alts ->
           CaseE inf (go scr) (map doalt alts)
      
    doalt a = a {altBody = go $ altBody a}
    dofun f = f {funBody = go $ funBody f}

specializeCall inf op args = 
  case op
  of VarE {} -> specializeTyAppExp op >>= specialize_args
     TyAppE {} -> specializeTyAppExp op >>= specialize_args
     _ -> specializeMaybe op >>= specialize_args . spclTyAppFromMaybe
  where
    specialize_args ErasedTyApp = return Nothing
    specialize_args (SpclDictExp e) = return (Just e)
    specialize_args (SpclTyApp op') = do
      -- Specialize arguments and rebuild the call expression
      args' <- mapM specializeMaybe args
      return $ Just $ CallE { expInfo = inf
                            , expOper = op'
                            , expArgs = catMaybes args'}

-- | The result of specializing a type application
data SpclTyApp =
    ErasedTyApp                 -- ^ This term was erased
  | SpclTyApp !RExp             -- ^ The specialized expression
  | SpclDictExp !RExp           -- ^ A dictionary constructor expression 
                                --   that was replaced by a global value.
                                --   The original constructor arguments
                                --   should be erased.

-- | Translate the result of a specialization to the result of a type
--   application specialization.  The result is an erased or a specialized
--   term; it can't be a specialized dictionary constructor.
spclTyAppFromMaybe :: Maybe RExp -> SpclTyApp
spclTyAppFromMaybe Nothing  = ErasedTyApp
spclTyAppFromMaybe (Just e) = SpclTyApp e

-- | Specialize an expression consisting of a series of type applications,
--   in a non-function-call context.
specializeTyAppExpNonCall expression =
  specializeTyAppExp expression >>= make_expression
  where
    make_expression ErasedTyApp     = return Nothing
    make_expression (SpclTyApp e)   = return (Just e)
    make_expression (SpclDictExp e) =
      internalError "specialize: Dictionary constructor lacks parameters"

-- | Specialize an expression consisting of a series of type applications.
--
-- If this expression is a @TraversableDict Stream@, then remove it.
specializeTyAppExp expression = do
  traversable_dict_param <- matchTraversableDictCall expression
  case traversable_dict_param of
    Just (SFType (VarT c))
      | c `isPyonBuiltin` the_Stream ->
          -- Remove Stream dictionaries
          return ErasedTyApp
      | c `isPyonBuiltin` the_list ->
          -- Replace with a list dictionary
          let dict_expr = VarE { expInfo = internalSynInfo ObjectLevel
                               , expVar = pyonBuiltin the_OpaqueTraversableDict_list}
          in return $ SpclDictExp dict_expr
      | otherwise -> internalError "Cannot specialize Traversable dictionary"
    Nothing -> do
      -- Specialize the operator based on type arguments
      operator <- specializeOperator expression
  
      -- Revisit the expression and specialize or discard the arguments
      case operator of
        Nothing -> return ErasedTyApp
        Just (op, arg_poss) ->
          fmap SpclTyApp $ specialize_args op arg_poss expression
  where
    specialize_args operator (arg_pos:arg_poss') e =
      case e
      of TyAppE {expInfo = inf, expOper = op, expTyArg = arg} -> do
           op' <- specialize_args operator arg_poss' op
           
           -- If the flag is False, discard the argument; otherwise
           -- evaluate it
           case arg_pos of
             False -> return op'
             True -> do
               arg' <- specializeType arg
               return $ TyAppE {expInfo = inf, expOper = op', expTyArg = arg'}

         _ -> internalError "specializeTyAppExp"

    specialize_args operator [] e =
      case e
      of TyAppE {} -> internalError "specializeTyAppExp"
         _ -> return operator

-- | Look up and compute the specialization of a type application.
-- Because we started from a HM language with dictionary passing, the operator
-- will always be a variable or constructor.
-- 
-- If the operator is not eliminated by specialization, the return value 
-- consists of the specialized operator and the positions of the 
-- value operands that are kept (other positions are discarded).  
--
-- N.B. If we ever have dictionary members that have a traversable parameter,
-- we'll need to do something more sophisticated here.  For now, we just abort.
specializeOperator :: RExp -> Spcl (Maybe (RExp, [Bool]))
specializeOperator exp = spcl [] exp
  where 
    spcl tl expr =
      case expr
      of TyAppE {expOper = op, expTyArg = arg} -> do
           spcl (arg : tl) op

         VarE {expInfo = inf, expVar = v} -> do
           tbl <- lookupVarSpclTable v
           val <- pickFullSpecialization tbl tl
           case val of
             Nothing -> return Nothing
             Just (keep_args, v) ->
               return $ Just (VarE {expInfo = inf , expVar = v},
                              keep_args)

         _ -> internalError "specializeTyApp: Unexpected type application"

specializeAlt :: RAlt -> Spcl RAlt
specializeAlt alternative = do
  ty_args <- mapM specializeType $ altTyArgs alternative

  -- Add constructor-bound parameters to the environment.  We assume that
  -- constructors never contain dictionaries.
  binders' <- mapM specialize_param $ altParams alternative
  assumePats binders' $ do
    body <- specialize $ altBody alternative
    return $ alternative { altTyArgs = ty_args
                         , altParams = binders'
                         , altBody = body}
  where
    specialize_param (VarP var ty) = do
      ty' <- specializeType ty
      return (VarP var ty')

-- | Specialize a monomorphic function
specializeFun :: RFun -> Spcl RFun
specializeFun function
  | not $ null $ funTyParams function =
      internalError "specializeFun: Function is polymorphic"
  | otherwise = do
      specializeAndAssumePats (funParams function) $ \params -> do
        return_type <- specializeType $funReturnType function
        body <- specialize $ funBody function
        return $ function { funParams = params
                          , funReturnType = return_type
                          , funBody = body}

-- | Specialize a polymorphic function.  Create a new function definition for
-- each specialized instance.
specializePolymorphicFun :: SpclTable -> Def Rec -> Spcl [Def Rec]
specializePolymorphicFun tbl (Def orig_var orig_fun) =
  go tbl [] (funTyParams orig_fun)
  where
    -- Specialize according to the specialization table.
    -- Add parameters to the environment as we go.
    go (Don'tCare tbl) s_params (param@(TyPat tv k) : params) =
      assumeType tv Don'tCareType $
      go tbl (param : s_params) params
    
    go (Specialize l r) s_params (param@(TyPat tv k) : params) = do
      -- Specialize to stream type.  This parameter disappears.
      defs1 <- assumeType tv IsStreamType $
               go l s_params params

      -- Specialize to non-stream type.
      defs2 <- assumeType tv NotStreamType $
               go r (param:s_params) params

      return $ defs1 ++ defs2
    
    go (End v) s_params [] = do
      def <- specialize_instance v (reverse s_params)
      return [def]

    go (End _) _ _ =
      internalError "specializePolymorphicFun: too many parameters"

    go _ _ [] =
      internalError "specializePolymorphicFun: too few parameters"

    -- Specialize one instance of the function, with the given type parameters,
    -- to the given derived name
    specialize_instance derived_name s_params = do
      specializeAndAssumePats (funParams orig_fun) $ \params -> do
        return_type <- specializeType $ funReturnType orig_fun
        body <- specialize $ funBody orig_fun

        let new_fun = orig_fun { funTyParams = s_params
                               , funParams = params
                               , funReturnType = return_type
                               , funBody = body}
        return $ Def derived_name new_fun

-- | Create a specialization table from the given signature.  An element of
-- the signature is @True@ if it is used for specialization, @False@
-- otherwise.
createSpclTable :: Spcl Var -> [Bool] -> Spcl SpclTable
createSpclTable mk_entry sig = create sig
  where
    create (True : sig)  = liftM2 Specialize (create sig) (create sig)
    create (False : sig) = liftM Don'tCare (create sig)
    create []            = liftM End mk_entry

-- | Create a function's specialization table.  Based on the function's 
-- parameters, create a table and new variables for all possible 
-- specializations.  The actual functions aren't created.
createFunSpclTable :: Def Rec -> Spcl SpclTable
createFunSpclTable (Def fun_name function) = let 
  -- Find type variables that are parameters of Traversable dictionary types
  -- in the parameter list
  traversable_variables =
    mapMaybe traversable_dict_parameter $ funParams function
  
  -- Find the type parameters to specialize on
  specializable_type_parameters =
    [v `elem` traversable_variables | TyPat v _ <- funTyParams function]
    
  in create_table specializable_type_parameters
  where
    -- Create a specialization table.  As a special case, if the function is
    -- not specialized on any parameters, don't rename it.
    create_table sig 
      | all (False ==) sig = return $
                             foldr (const Don'tCare) (End fun_name) sig
      | otherwise = createSpclTable make_new_var sig
    
    traversable_dict_parameter (VarP _ ty) = traversableDictTypeParameter ty
    
    -- Create a new function name
    make_new_var = newClonedVar fun_name
      
specializeDefs :: DefGroup Rec -> Spcl a -> Spcl (DefGroup Rec, a)
specializeDefs dg m = do
  -- Create specialization tables for each function
  tables <- mapM createFunSpclTable dg

  -- Add variables to environment
  add_tables_to_environment tables dg $ do
    -- Specialize the functions
    (concat -> new_defs) <- zipWithM specializePolymorphicFun tables dg

    x <- m
    return (new_defs, x)
  where
    add_tables_to_environment tables dg m =
      foldr add_table_to_environment m $ zip tables dg

    add_table_to_environment (table, Def v _) m =
      assumeVarSpclTable v table m

specializeExport :: Export Rec -> Spcl (Export Rec)
specializeExport (Export pos spec f) = do
  f' <- specializeFun f
  return (Export pos spec f')

specializeTopLevelDefs :: [DefGroup Rec] 
                       -> [Export Rec]
                       -> Spcl ([DefGroup Rec], [Export Rec])
specializeTopLevelDefs (dg:dgs) exports = do
  (dg', (dgs', exports')) <-
    specializeDefs dg $ specializeTopLevelDefs dgs exports
  return (dg' : dgs', exports')

specializeTopLevelDefs [] exports = do
  exports' <- mapM specializeExport exports
  return ([], exports')

specializeModule :: RModule -> Spcl RModule
specializeModule (Module module_name defs exports) = do
  (defs', exports') <- specializeTopLevelDefs defs exports
  return $ Module module_name defs' exports'

doSpecialization :: RModule -> IO RModule
doSpecialization mod =
  withTheNewVarIdentSupply $ \supply ->
  runSpcl supply $ specializeModule mod
