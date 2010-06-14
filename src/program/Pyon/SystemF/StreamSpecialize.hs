{-| After optimizations at the System F level to get rid of superfluous
-- class dictionaries, we specialize all appearances of the Traversable 
-- class into stream-traversing and data-structure-traversing cases.
-- After specialization, streams are no longer a member of the Traversable 
-- class.  Effect inference requires this.
-}

{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, ViewPatterns #-}
module Pyon.SystemF.StreamSpecialize(doSpecialization)
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
import qualified Gluon.Core as Gluon
import Gluon.Core(Var, varName, varID, Con, conID)

import Pyon.Globals
import Pyon.SystemF.Builtins
import Pyon.SystemF.Print
import Pyon.SystemF.Syntax

-- | A specialization table is stored as a trie.  At each level, inspect one
-- type parameter and take a branch.
data SpclTable a =
    Don'tCare !(SpclTable a)
    -- ^ Specialize (is stream) (is not stream)
  | Specialize !(SpclTable a) !(SpclTable a)
  | End a

showSpclTable :: SpclTable a -> Doc
showSpclTable (Don'tCare x) =
  hang (text "Don'tCare") 2 $ showSpclTable x
showSpclTable (Specialize l r) =
  hang (text "Specialize") 2 $ showSpclTable l $$ showSpclTable r
showSpclTable (End a) = text "End"

instance Functor SpclTable

-- | Properties of a type that are important to specialization.
data SpclType =
    Don'tCareType                 -- ^ Doesn't particpate in specialization
  | IsStreamType                  -- ^ Is a stream
  | NotStreamType                 -- ^ Is not a stream
    deriving(Eq, Show)

pickSpecialization :: SpclType -> SpclTable a -> SpclTable a
pickSpecialization ty tbl =
  case ty
  of Don'tCareType ->
       case tbl of Don'tCare x -> x
                   _ -> wrong
     IsStreamType ->
       case tbl of Specialize l _ -> l
                   _ -> wrong
     NotStreamType ->
       case tbl of Specialize _ r -> r
                   _ -> wrong
  where
    wrong = internalError "pickSpecialization"

finishSpecialization :: SpclTable a -> a
finishSpecialization (End x) = x
finishSpecialization _ = internalError "finishSpecialization"

-- | If the type is a traversable dictionary type, return the type parameter,
-- which must be a type variable.  Otherwise, return Nothing.
traversableDictTypeParameter :: RType -> Maybe Var
traversableDictTypeParameter ty =
      case ty
      of Gluon.AppE { Gluon.expOper = Gluon.ConE {Gluon.expCon = c}
                    , Gluon.expArgs = [arg]}
           | c `isPyonBuiltin` the_TraversableDict ->
               -- Argument must be a type variable
               case arg
               of Gluon.VarE {Gluon.expVar = v} -> Just v
                  _ -> internalError "traversableDictTypeParameter: Unexpected traversable dictionary type"
         _ -> Nothing
  
traversableDictTypeParameter _ = internalError "traversableDictTypeParameter"

globalConTable :: IntMap.IntMap (SpclTable Con)
globalConTable =
  IntMap.fromList [(fromIdent $ conID $ pyonBuiltin c, tbl) | (c, tbl) <- assocs]
  where
    -- Create an entry that is not specialized.  The 'arity' is the number of 
    -- type parameters the entry takes.
    unchanged arity field =
      (field, don't_cares arity $ pyonBuiltin field)
      where
        don't_cares n x = iterate Don'tCare (End x) !! n

    assocs =
      [ unchanged 0 the_passConv_int
      , unchanged 0 the_passConv_float
      , unchanged 0 the_passConv_bool
      , unchanged 0 the_passConv_NoneType
      , unchanged 1 the_passConv_iter
      , unchanged 1 the_passConv_list
      , unchanged 0 the_passConv_Any
      , unchanged 0 (eqMember . the_EqDict_int)
      , unchanged 0 (neMember . the_EqDict_int)
      , unchanged 0 (eqMember . the_EqDict_float)
      , unchanged 0 (neMember . the_EqDict_float)
      , unchanged 0 (zeroMember . the_AdditiveDict_int)
      , unchanged 0 (addMember . the_AdditiveDict_int)
      , unchanged 0 (subMember . the_AdditiveDict_int)
      , unchanged 0 (zeroMember . the_AdditiveDict_float)
      , unchanged 0 (addMember . the_AdditiveDict_float)
      , unchanged 0 (subMember . the_AdditiveDict_float)

      , (unchanged 1 (traverseMember . the_TraversableDict_Stream)
      , unchanged 2 the_oper_CAT_MAP
      , unchagned 1 the_oper_DO
      ]

-------------------------------------------------------------------------------

newtype Spcl a = Spcl (ReaderT SpclEnv IO a) deriving(Monad)

runSpcl :: IdentSupply Var -> Spcl a -> IO a
runSpcl supply (Spcl m) =
  let env = SpclEnv supply IntMap.empty IntMap.empty globalConTable
  in runReaderT m env

data SpclEnv =
  SpclEnv
  { spclEnvVarIDs :: !(IdentSupply Var)
  , spclEnvTypes :: IntMap.IntMap SpclType
  , spclEnvVarTable :: IntMap.IntMap (SpclTable Var)
  , spclEnvConTable :: IntMap.IntMap (SpclTable Con)
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

lookupType :: Var -> Spcl SpclType
lookupType v = spclAsks $ \env ->
  case IntMap.lookup (fromIdent $ varID v) $ spclEnvTypes env
  of Nothing -> internalError "lookupType: No information for type variable"
     Just x  -> x

assumeVarSpclTable :: Var -> SpclTable Var -> Spcl a -> Spcl a
assumeVarSpclTable v tbl m = spclLocal add_entry m
  where
    add_entry env =
      env {spclEnvVarTable =
              IntMap.insert (fromIdent $ varID v) tbl $ spclEnvVarTable env}

lookupVarSpclTable :: Var -> Spcl (SpclTable Var)
lookupVarSpclTable v = spclAsks $ \env ->
  case IntMap.lookup (fromIdent $ varID v) $ spclEnvVarTable env
  of Nothing -> internalError "lookupVarSpclTable: No information for variable"
     Just x  -> x

lookupConSpclTable :: Con -> Spcl (SpclTable Con)
lookupConSpclTable c = spclAsks $ \env ->
  case IntMap.lookup (fromIdent $ conID c) $ spclEnvConTable env
  of Nothing -> internalError $ "lookupConSpclTable: No information for constructor " ++ showLabel (Gluon.conName c)
     Just x  -> x

-- | Specialize a type.  Type variables that have been specialized to 'Stream'
-- in the current context are replaced with 'Stream'.
specializeType :: RType -> Spcl RType
specializeType ty =
  case ty
  of Gluon.VarE {Gluon.expVar = v} -> do
       spcl_type <- lookupType v
       case spcl_type of
         IsStreamType -> return $ stream_type $ Gluon.getSourcePos ty
         _            -> return ty
     _ -> Gluon.traverseExp specializeType do_tuple do_sum ty
  where
    stream_type pos = Gluon.mkConE pos $ pyonBuiltin the_Stream
    do_tuple = Gluon.traverseTuple specializeType do_tuple
    do_sum = Gluon.traverseSum specializeType do_sum

-- | Determine how to specialize based on this type
getTypeSignature :: RType -> Spcl SpclType
getTypeSignature (Gluon.VarE {Gluon.expVar = v}) = lookupType v
getTypeSignature _ = return Don'tCareType

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
assumePat (VarP v _) m = assumeVarSpclTable v (End v) m

assumePats :: [RPat] -> Spcl a -> Spcl a
assumePats ps m = foldr assumePat m ps

specialize :: RExp -> Spcl RExp
specialize expression =
  case expression
  of VarE {} -> specializeTyAppExp expression
     ConE {} -> specializeTyAppExp expression
     LitE {expType = ty} -> do
       ty' <- specializeType ty
       return $ expression {expType = ty'}
     TyAppE {} -> specializeTyAppExp expression
     CallE {expInfo = inf, expOper = op, expArgs = args} -> do
       -- TODO: get rid of dictionary arguments when specializing streams
       op' <- specialize op
       args' <- mapM specialize args
       return $ CallE {expInfo = inf, expOper = op', expArgs = args'}
     FunE {expInfo = inf, expFun = f} -> do
       f' <- specializeFun f
       return $ FunE {expInfo = inf, expFun = f'}
     LetE {expInfo = inf, expBinder = b, expValue = rhs, expBody = body} -> do
       rhs' <- specialize rhs

       -- The local variable is never a dictionary, so it's never eliminated
       Just b' <- specializePat b
       body' <- assumePat b' $ specialize body
       return $ LetE { expInfo = inf
                     , expBinder = b'
                     , expValue = rhs'
                     , expBody = body'}
     LetrecE {expInfo = inf, expDefs = defs, expBody = body} -> do
       (defs', body') <- specializeDefs defs $ specialize body
       return $ LetrecE {expInfo = inf, expDefs = defs', expBody = body'}
     CaseE {expInfo = inf, expScrutinee = scr, expAlternatives = alts} -> do
       scr' <- specialize scr
       alts' <- mapM specializeAlt alts
       return $ CaseE { expInfo = inf
                      , expScrutinee = scr
                      , expAlternatives = alts}

specializeTyAppExp expression = do
  -- Specialize the operator based on type arguments
  operator <- specializeOperator expression
  
  -- Revisit the expression and specialize the arguments
  specialize_args operator expression
  where
    specialize_args operator e = 
      case e
      of TyAppE {expInfo = inf, expOper = op, expTyArg = arg} -> do
           arg' <- specializeType arg
           op' <- specialize_args operator op
           return $ TyAppE {expInfo = inf, expOper = op', expTyArg = arg'}

         _ -> return operator

-- | Look up and compute the specialization of a type application.
-- Because we started from a HM language with dictionary passing, the operator
-- will always be a variable, constructor, or dictionary entry.
--
-- N.B. If we ever have dictionary members that have a traversable parameter,
-- we'll need to do something more sophisticated here.  For now, we just abort.
specializeOperator :: RExp -> Spcl RExp
specializeOperator exp = spcl [] exp
  where 
    spcl tl expr = 
      case expr
      of TyAppE {expOper = op, expTyArg = arg} -> do
           ty <- getTypeSignature arg
           spcl (ty : tl) op

         VarE {expInfo = inf, expVar = v} -> do
           tbl <- lookupVarSpclTable v
           return $ VarE { expInfo = inf
                         , expVar = finishSpecialization $
                                    foldr pickSpecialization tbl tl}

         ConE {expInfo = inf, expCon = c} -> do
           tbl <- lookupConSpclTable c
           return $ ConE { expInfo = inf
                         , expCon = finishSpecialization $
                                    foldr pickSpecialization tbl tl}

         _ ->
           -- This is probably a class dictionary member. 
           -- As long as all parmeters are "don't care" parameters,
           -- we don't have to specialize the expression.
           if all (Don'tCareType ==) tl
           then specialize expr
           else internalError "specializeTyApp: Unexpected type application"

specializeAlt :: RAlt -> Spcl RAlt
specializeAlt alternative = do
  body <- specialize $ altBody alternative
  return $ alternative {altBody = body}

-- | Specialize a monomorphic function
specializeFun :: RFun -> Spcl RFun
specializeFun function
  | not $ null $ funTyParams function =
      internalError "specializeFun: Function is polymorphic"
  | otherwise = do
      (catMaybes -> params) <- mapM specializePat $ funParams function
      return_type <- specializeType $ funReturnType function
      
      -- Assume function parameters while specializing body
      body <- assumePats params $ specialize $ funBody function
      return $ function { funParams = params
                        , funReturnType = return_type
                        , funBody = body}

-- | Specialize a polymorphic function.  Create a new function definition for
-- each specialized instance.
specializePolymorphicFun :: SpclTable Var -> Def Rec -> Spcl [Def Rec]
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
      def <- specialize_instance v s_params
      return [def]

    go (End _) _ _ =
      internalError "specializePolymorphicFun: too many parameters"

    go _ _ [] =
      internalError "specializePolymorphicFun: too few parameters"

    -- Specialize one instance of the function, with the given type parameters,
    -- to the given derived name
    specialize_instance derived_name s_params = do
      (catMaybes -> params) <- mapM specializePat $ funParams orig_fun
      return_type <- specializeType $ funReturnType orig_fun
      body <- assumePats params $ specialize $ funBody orig_fun

      let new_fun = orig_fun { funTyParams = s_params
                             , funParams = params
                             , funReturnType = return_type
                             , funBody = body}
      return $ Def derived_name new_fun

-- | Create a specialization table from the given signature.  An element of
-- the signature is @True@ if it is used for specialization, @False@
-- otherwise.
createSpclTable :: Spcl a -> [Bool] -> Spcl (SpclTable a)
createSpclTable mk_entry sig = create sig
  where
    create (True : sig)  = liftM2 Specialize (create sig) (create sig)
    create (False : sig) = liftM Don'tCare (create sig)
    create []            = liftM End mk_entry

-- | Create a function's specialization table.  Based on the function's 
-- parameters, create a table and new variables for all possible 
-- specializations.  The actual functions aren't created.
createFunSpclTable :: Def Rec -> Spcl (SpclTable Var)
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
    make_new_var = Gluon.newVar (varName fun_name) Gluon.ObjectLevel
      
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

specializeTopLevelDefs :: [DefGroup Rec] -> Spcl [DefGroup Rec]
specializeTopLevelDefs (dg:dgs) = do
  (dg', dgs') <- specializeDefs dg $ specializeTopLevelDefs dgs
  return $ dg' : dgs'

specializeTopLevelDefs [] = return []

specializeModule :: Module Rec -> Spcl (Module Rec)
specializeModule (Module defs exports) = do
  defs' <- specializeTopLevelDefs defs
  
  -- FIXME: specialization on exported functions
  return $ Module defs' exports

doSpecialization :: RModule -> IO RModule
doSpecialization mod =
  withTheVarIdentSupply $ \supply ->
  runSpcl supply $ specializeModule mod
