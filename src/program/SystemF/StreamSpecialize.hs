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

import Common.Error
import Common.Identifier
import Common.Label
import Common.SourcePos
import Common.Supply

import Globals
import Builtins.Builtins
import SystemF.Print
import SystemF.Syntax
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
traversableDictTypeParameter :: TypSF -> Maybe Var
traversableDictTypeParameter (TypSF ty) =
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
      , unchanged 1 the_repr_Boxed
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
      , unchanged 0 the_None
      , unchanged 0 the_True
      , unchanged 0 the_False
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
unchangedType :: TypSF -> Var -> SpclTable
unchangedType (TypSF ty) x = add_don't_cares ty (End x)
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

specializeRet :: RetSF -> Spcl RetSF
specializeRet (RetSF ty) = fmap RetSF $ specializeType' ty

-- | Specialize a type.  Type variables that have been specialized to 'Stream'
-- in the current context are replaced with 'Stream'.
--
-- N.B. We assume the type is not stream-polymorphic.
specializeType :: TypSF -> Spcl TypSF
specializeType (TypSF ty) = fmap TypSF $ specializeType' ty

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
pickSpecialization :: SpclTable -> TypSF -> Spcl (Bool, SpclTable)
pickSpecialization tbl ty =
  case tbl
  of Don'tCare x    -> return (True, x)
     Specialize l r -> do
       spcl_type <-
         case fromVarApp $ fromTypSF ty
         of Just (v, _) -> lookupType v
            _ -> return NotStreamType
       pick_one spcl_type l r
     _ -> wrong
  where
    pick_one IsStreamType  l _ = return (False, l)
    pick_one NotStreamType _ r = return (True, r)
    pick_one Don'tCareType _ _ = wrong
    wrong = internalError "pickSpecialization"

pickFullSpecialization :: SpclTable -> [TypSF] -> Spcl (Maybe ([Bool], Var))
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
specializePat :: PatSF -> Spcl (Maybe PatSF)
specializePat (VarP v ty) = 
  case traversableDictTypeParameter (TypSF ty)
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
       ty' <- specializeType (TypSF ty)
       return $ Just $ VarP v (fromTypSF ty')
       
specializePat _ = internalError "specializePat: Not a variable pattern"

-- | Assume a pattern-bound variable.  The variable will not be specialized.
assumePat :: PatSF -> Spcl a -> Spcl a
assumePat (VarP v t) m = assumeVarSpclTable v (unchangedType (TypSF t) v) m

assumePats :: [PatSF] -> Spcl a -> Spcl a
assumePats ps m = foldr assumePat m ps

specializeAndAssumePat :: PatSF -> (Maybe PatSF -> Spcl a) -> Spcl a
specializeAndAssumePat pat@(VarP v ty) k = do
  mpat' <- specializePat pat
  case mpat' of
    Nothing   -> assumeVarSpclTable v EliminatedDict $ k mpat'
    Just pat' -> assumePat pat' $ k mpat'

specializeAndAssumePats :: [PatSF] -> ([PatSF] -> Spcl a) -> Spcl a
specializeAndAssumePats ps k =
  withMany specializeAndAssumePat ps (k . catMaybes)

-- | Specialize an expression.
specialize :: ExpSF -> Spcl ExpSF
specialize expression = do
  e' <- specializeMaybe expression
  case e' of
    Nothing -> internalError "specialize: Not expecting a dictionary value here"
    Just e  -> return e

specializeMaybe :: ExpSF -> Spcl (Maybe ExpSF)
specializeMaybe expression =
  case fromExpSF expression
  of VarE {} -> specializeVar expression
     LitE {} -> return $ Just expression
     AppE {expInfo = inf, expOper = op, expTyArgs = ty_args, expArgs = args} -> 
       specializeCall inf op ty_args args
     LamE {expInfo = inf, expFun = f} -> do
       f' <- specializeFun f
       return $ Just $ ExpSF $ LamE {expInfo = inf, expFun = f'}
     LetE {expInfo = inf, expBinder = b, expValue = rhs, expBody = body} -> do
       rhs' <- specialize rhs

       -- The local variable is never a dictionary, so it's never eliminated
       Just b' <- specializePat b
       body' <- assumePat b' $ specialize body
       return $ Just $ ExpSF $ LetE { expInfo = inf
                                    , expBinder = b'
                                    , expValue = rhs'
                                    , expBody = body'}
     LetrecE {expInfo = inf, expDefs = defs, expBody = body} -> do
       (defs', body') <- specializeDefs defs $ specialize body
       return $ Just $ ExpSF $ LetrecE { expInfo = inf
                                       , expDefs = defs'
                                       , expBody = body'}
     CaseE {expInfo = inf, expScrutinee = scr, expAlternatives = alts} -> do
       mscr' <- specializeMaybe scr
       case mscr' of
         Just scr' -> do
           alts' <- mapM specializeAlt alts
           return $ Just $ ExpSF $ CaseE { expInfo = inf
                                         , expScrutinee = scr
                                         , expAlternatives = alts'}
         Nothing ->
           -- Deconstructing a traversable object dictionary.  Replace the
           -- pattern variables with stream-specific members.
           case alts
           of [alt] -> specializeDictionaryAlternative alt

-- | Specialize a VarE expression.  Treat it like an instantiation with zero
-- type arguments.
specializeVar expression =
  specializeTyAppExp expression [] >>= make_expression
  where
    make_expression ErasedTyApp        = return Nothing
    make_expression (SpclTyApp e [])   = return $ Just e
    make_expression (SpclTyApp e args) =
      return $ Just $ ExpSF $ AppE (expInfo $ fromExpSF e) e args []
    make_expression (SpclDictExp e) =
      internalError "specialize: Dictionary constructor lacks parameters"


specializeDictionaryAlternative (AltSF (Alt { altTyArgs = [_]
                                            , altParams = [VarP traverse_var _,
                                                           VarP build_var _]
                                            , altBody = body
                                            })) =
  let body' = substituteTraversableMethods traverse_var build_var body
  in specializeMaybe body'

-- | Replace any occurences of dictionary methods with the
--   stream build and traverse methods.
substituteTraversableMethods traverse_var build_var expr = go expr
  where
    go expr =
      case fromExpSF expr
      of VarE {expInfo = inf, expVar = v}
           | v == traverse_var ->
             ExpSF $ VarE {expInfo = inf, 
                           expVar = pyonBuiltin the_TraversableDict_Stream_traverse}
           | v == build_var ->
             ExpSF $ VarE {expInfo = inf,
                           expVar = pyonBuiltin the_TraversableDict_Stream_build}
           | otherwise -> expr
         LitE {} -> expr
         AppE inf op ty_args args ->
           ExpSF $ AppE inf (go op) ty_args (map go args)
         LamE inf f ->
           ExpSF $ LamE inf $ dofun f
         LetE inf b rhs body ->
           ExpSF $ LetE inf b (go rhs) (go body)
         LetrecE inf defs b ->
           ExpSF $ LetrecE inf [Def v (dofun f) | Def v f <- defs] (go b)
         CaseE inf scr alts ->
           ExpSF $ CaseE inf (go scr) (map doalt alts)
      
    doalt (AltSF a) = AltSF $ a {altBody = go $ altBody a}
    dofun (FunSF f) = FunSF $ f {funBody = go $ funBody f}

specializeCall inf op ty_args args =
  specializeTyAppExp op ty_args >>= specialize_args
  where
    specialize_args ErasedTyApp = return Nothing
    specialize_args (SpclDictExp e) = return (Just e)
    specialize_args (SpclTyApp op' ty_args') = do
      -- Specialize arguments and rebuild the call expression
      args' <- mapM specializeMaybe args
      return $ Just $ ExpSF $ AppE { expInfo = inf
                                   , expOper = op'
                                   , expTyArgs = ty_args'
                                   , expArgs = catMaybes args'}

-- | The result of specializing a type application
data SpclTyApp =
    ErasedTyApp                 -- ^ This term was erased
  | SpclTyApp !ExpSF [TypSF]     -- ^ The specialized expression
  | SpclDictExp !ExpSF           -- ^ A dictionary constructor expression 
                                --   that was replaced by a global value.
                                --   The original constructor arguments
                                --   should be erased.

-- | Specialize an instantiated expression.  Based on the operator and 
--   type arguments, pick a new operator and new type arguments, or erase
--   the expression entirely.
--
-- If this expression is a @TraversableDict Stream@, then remove it.
specializeTyAppExp (ExpSF op) ty_args 
  | VarE {expInfo = inf, expVar = op_var} <- op,
    op_var `isPyonBuiltin` the_traversableDict =
      case ty_args
      of [t] -> do t' <- specializeType t
                   specializeTraversableDictCall inf t'

  | VarE {expInfo = inf, expVar = op_var} <- op = do
      -- Specialize the operator based on type arguments
      operator <- specializeOperator inf op_var ty_args
  
      -- Revisit the expression and specialize or discard the arguments
      case operator of
        Nothing -> return ErasedTyApp
        Just (new_op, arg_poss) -> do
          -- Specialize the arguments that aren't be discarded
          spcl_args <-
            mapM specializeType [t | (True, t) <- zip arg_poss ty_args]
          return $ SpclTyApp new_op spcl_args

  | null ty_args = do
      -- Specialize the operator expression
      operator <- specializeMaybe (ExpSF op)
      case operator of
        Nothing -> return ErasedTyApp
        Just op' -> return (SpclTyApp op' [])

  | otherwise = internalError "specializeTyAppExp"

-- | Determine what to do for a Traversable dictionary, based on the
--   dictionary's type parameter.
specializeTraversableDictCall inf t =
  case t
  of TypSF (VarT c)
       | c `isPyonBuiltin` the_Stream ->
         -- Remove Stream dictionaries
         return ErasedTyApp
       | c `isPyonBuiltin` the_list ->
         -- Replace with a list dictionary
         let dict_expr = ExpSF $ VarE { expInfo = inf
                                      , expVar = list_dict}
         in return $ SpclDictExp dict_expr
     _ -> internalError "Cannot specialize Traversable dictionary"
  where
    list_dict = pyonBuiltin the_OpaqueTraversableDict_list

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
specializeOperator :: ExpInfo -> Var -> [TypSF] -> Spcl (Maybe (ExpSF, [Bool]))
specializeOperator inf v types = do
  tbl <- lookupVarSpclTable v
  val <- pickFullSpecialization tbl types
  case val of
    Nothing -> return Nothing
    Just (keep_args, v) ->
      return $ Just (ExpSF $ VarE {expInfo = inf , expVar = v}, keep_args)

specializeAlt :: AltSF -> Spcl AltSF
specializeAlt (AltSF alternative) = do
  ty_args <- mapM specializeType $ altTyArgs alternative

  -- Add constructor-bound parameters to the environment.  We assume that
  -- constructors never contain dictionaries.
  binders' <- mapM specialize_param $ altParams alternative
  assumePats binders' $ do
    body <- specialize $ altBody alternative
    return $ AltSF $ alternative { altTyArgs = ty_args
                                 , altParams = binders'
                                 , altBody = body}
  where
    specialize_param (VarP var ty) = do
      ty' <- specializeType (TypSF ty)
      return (VarP var (fromTypSF ty'))

-- | Specialize a monomorphic function
specializeFun :: FunSF -> Spcl FunSF
specializeFun (FunSF function)
  | not $ null $ funTyParams function =
      internalError "specializeFun: Function is polymorphic"
  | otherwise = do
      specializeAndAssumePats (funParams function) $ \params -> do
        return_type <- specializeRet $ funReturn function
        body <- specialize $ funBody function
        return $ FunSF (function { funParams = params
                                 , funReturn = return_type
                                 , funBody = body})

-- | Specialize a polymorphic function.  Create a new function definition for
-- each specialized instance.
specializePolymorphicFun :: SpclTable -> Def SF -> Spcl [Def SF]
specializePolymorphicFun tbl (Def orig_var (FunSF orig_fun)) =
  go tbl [] (funTyParams orig_fun)
  where
    -- Specialize according to the specialization table.
    -- Add parameters to the environment as we go.
    go (Don'tCare tbl) s_params (param@(TyPatSF tv k) : params) =
      assumeType tv Don'tCareType $
      go tbl (param : s_params) params
    
    go (Specialize l r) s_params (param@(TyPatSF tv k) : params) = do
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
        return_type <- specializeType $ TypSF $ retSFType $ funReturn orig_fun
        body <- specialize $ funBody orig_fun

        let new_fun = orig_fun { funTyParams = s_params
                               , funParams = params
                               , funReturn = RetSF (fromTypSF return_type)
                               , funBody = body}
        return $ Def derived_name (FunSF new_fun)

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
createFunSpclTable :: Def SF -> Spcl SpclTable
createFunSpclTable (Def fun_name (FunSF function)) = let 
  -- Find type variables that are parameters of Traversable dictionary types
  -- in the parameter list
  traversable_variables =
    mapMaybe traversable_dict_parameter $ funParams function
  
  -- Find the type parameters to specialize on
  specializable_type_parameters =
    [v `elem` traversable_variables | TyPatSF v _ <- funTyParams function]
    
  in create_table specializable_type_parameters
  where
    -- Create a specialization table.  As a special case, if the function is
    -- not specialized on any parameters, don't rename it.
    create_table sig 
      | all (False ==) sig = return $
                             foldr (const Don'tCare) (End fun_name) sig
      | otherwise = createSpclTable make_new_var sig
    
    traversable_dict_parameter (VarP _ ty) =
      traversableDictTypeParameter (TypSF ty)
    
    -- Create a new function name
    make_new_var = newClonedVar fun_name
      
specializeDefs :: DefGroup SF -> Spcl a -> Spcl (DefGroup SF, a)
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

specializeExport :: Export SF -> Spcl (Export SF)
specializeExport (Export pos spec f) = do
  f' <- specializeFun f
  return (Export pos spec f')

specializeTopLevelDefs :: [DefGroup SF] 
                       -> [Export SF]
                       -> Spcl ([DefGroup SF], [Export SF])
specializeTopLevelDefs (dg:dgs) exports = do
  (dg', (dgs', exports')) <-
    specializeDefs dg $ specializeTopLevelDefs dgs exports
  return (dg' : dgs', exports')

specializeTopLevelDefs [] exports = do
  exports' <- mapM specializeExport exports
  return ([], exports')

specializeModule :: Module SF -> Spcl (Module SF)
specializeModule (Module module_name defs exports) = do
  (defs', exports') <- specializeTopLevelDefs defs exports
  return $ Module module_name defs' exports'

doSpecialization :: Module SF -> IO (Module SF)
doSpecialization mod =
  withTheNewVarIdentSupply $ \supply ->
  runSpcl supply $ specializeModule mod
