{-| Unpacking transformation.

This converts traversals over /lists/ to traversals over /arrays/ by
unpacking each list into a (size, array) pair.  Data structures are 
unpacked (replaced by functions that directly access their fields)
wherever a traversal is seen.  The actual unpacking code is floated out
to where the structure is defined.
-}

{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving #-}
module Core.Unpacking(unpackDataStructures)
where

import Prelude hiding(mapM)

import Control.Monad hiding(mapM)
import Control.Monad.Reader hiding(mapM)
import qualified Data.Map as Map
import Data.Monoid
import qualified Data.Set as Set
import Data.Traversable

import Gluon.Common.Error
import Gluon.Common.SourcePos
import Gluon.Common.Identifier
import Gluon.Common.Supply
import Gluon.Core.Level
import qualified Gluon.Core as Gluon
import qualified Gluon.Core.Builtins as Gluon
import Gluon.Core(SynInfo, Var, Rec)
import qualified SystemF.Builtins as SF
import Core.Syntax
import Globals

-- | Some effect types should be reconstructed, but we haven't implemented
--   that.  For those effect types, we use this.
unknown_effect :: RCType
unknown_effect = conCT (Gluon.builtin Gluon.the_EmpE)

nothingAnd m = fmap ((,) ()) m

-- | Information about a variable that has been unpacked.  Unpacking replaces
--   uses of an object with uses of some other objects, representing its
--   fields.
data UnpackedVar =
  AsUnpackedList !UnpackedList
  
data UnpackedList =
  UnpackedList
  { -- | The list's size, an @int@
    listSize :: Var
    -- | The list data address, an @Addr@
  , listDataAddr :: Var
    -- | The list data pointer, a @Ptr@
  , listDataPtr :: Var
  }

-- | A map that associates each address with its unpacked equivalent
-- (if it was unpacked).  The map holds all variables that are in the
-- environment and have been selected for unpacking.
type UnpackMap = Map.Map Var UnpackedVar

-- | State of the 'U' monad
type US = UnpackMap

-- | Remove an address variable from the unpacking map 
removeFromUS :: Var -> US -> US
removeFromUS v m = Map.delete v m

-- | Writer-style output of the 'U' monad.
--
--   Whenever code is unpacked, we keep track of which addresses
--   were used in an unpacked manner.  These sets tell us how to
--   update effect types. 
--
--   With the exception of variables that are unpacked, all
--   pass-by-reference address variables are considered \"packed\" and
--   will show up in \"packedUses\".  All other variables don't
--   show up here.
data UW =
  UW
  { unpackedUses :: Set.Set Var
  , packedUses   :: Set.Set Var
  }

-- | Remove an address variable from the output of a stage
removeFromUW :: Var -> UW -> UW
removeFromUW a (UW s1 s2) = UW (Set.delete a s1) (Set.delete a s2)

instance Monoid UW where
  mempty = UW Set.empty Set.empty
  mappend (UW u1 p1) (UW u2 p2) = UW (u1 `mappend` u2) (p1 `mappend` p2)

-- | Unpacking monad.
newtype U a = U {runU :: IdentSupply Var -> US -> IO (US, UW, a)}

instance Functor U where
  fmap f m = U $ \env st -> do (st', w, x) <- runU m env st
                               return (st', w, f x)

instance Monad U where
  return x = U $ \_ s -> return (s, mempty, x)
  m >>= k = U $ \env s -> do (s', w1, x) <- runU m env s
                             (s'', w2, y) <- runU (k x) env s'
                             return (s'', w1 `mappend` w2, y)

instance Supplies U (Ident Var) where
  fresh = U (\var_ids s -> do x <- supplyValue var_ids  
                              return (s, mempty, x))

-- | Run some code in an environment where the variables are bound to a list.
--
--   If the bound variable gets unpacked, generate the unpacking code here.
withListVariable :: Var          -- ^ Parameter address variable
                 -> Var          -- ^ Parameter pointer variable
                 -> RCType       -- ^ Type of list elements
                 -> U (a, RCExp) -- ^ Code transformation
                 -> U (a, RCExp) -- ^ Code transformation with unpacking
withListVariable a p elt_type m = U $ \env state -> do
  (state', effects, (x, exp)) <- runU m env state
  
  -- If list was used unpacked, then generate unpacking code
  let pos = getSourcePos exp
  exp' <- if a `Set.member` unpackedUses effects
          then case Map.lookup a state'
               of Just (AsUnpackedList ulist) ->
                    runGenIO env $ genListUnpack pos a p elt_type ulist exp
                  _ -> internalError "withListVariable"
          else return exp
  
  -- Remove the variable from state and effects
  let clean_state   = removeFromUS a state'
      clean_effects = removeFromUW a effects
  
  return (clean_state, clean_effects, (x, exp'))

-- | Run some code in an environment where the variables are bound to a
--   reference object that's ignored by unpacking.
withOtherVariable :: Var -> Var -> U a -> U a
withOtherVariable a p m = U $ \env state -> do
  (state', effects, x) <- runU m env state
  
  -- Remove the variable from state and effects
  let clean_state   = removeFromUS a state'
      clean_effects = removeFromUW a effects
  
  return (clean_state, clean_effects, x)

-- | Given a list address variable, get or create variables for the unpacked 
-- list.
unpackList :: Var -> U UnpackedList
unpackList addr = U $ \env st ->
  -- Do we already have an entry for this variable?
  case Map.lookup addr st
  of Just (AsUnpackedList ul) -> return (st, mempty, ul)
     Just _ -> internalError "unpackList: Unpacked as something else"
     Nothing -> do
       -- Create a new entry
       let label = Gluon.varName addr
       id1 <- supplyValue env
       id2 <- supplyValue env
       id3 <- supplyValue env
       let size_var = Gluon.mkVar id1 label ObjectLevel
       let data_addr_var = Gluon.mkVar id2 label ObjectLevel
       let data_ptr_var = Gluon.mkVar id3 label ObjectLevel
       
       -- Update state
       let ulist = UnpackedList { listSize = size_var
                                , listDataAddr = data_addr_var
                                , listDataPtr = data_ptr_var}
           st' = Map.insert addr (AsUnpackedList ulist) st

       return (st', mempty, ulist)

-- | Record that a packed use of this variable has occurred
usePacked :: Var -> U ()
usePacked v = U $ \_ st -> return (st, effect, ())
  where
    effect = mempty {packedUses = Set.singleton v}

-- | Record that an unpacked use has occurred
useUnpacked :: Var -> U ()
useUnpacked v = U $ \_ st -> return (st, effect, ())
  where
    effect = mempty {unpackedUses = Set.singleton v}

-------------------------------------------------------------------------------
-- Unpacking on Core expressions

unpackExp :: RCExp -> U RCExp
unpackExp expression =
  case expression
  of ValCE inf val -> unpackVal inf val
     AppCE inf op args ra -> unpackCall inf op args ra
     LamCE inf f -> do
       -- FIXME: This is potentially unsafe because the function can use
       -- unpacked variables, but it might be called outside the scope where
       -- unpacking was performed.
       --
       -- Need to come up with a strategy to avoid this.
       f' <- unpackFun f
       return (LamCE inf f')
     LetCE inf binder rhs body -> do
       rhs' <- unpackExp rhs
       (binder', body') <- unpackBinder binder $ unpackExp body
       return $ LetCE inf binder' rhs' body'
     LetrecCE inf defs body -> do
       defs' <- mapM unpackDef defs
       body' <- unpackExp body
       return $ LetrecCE inf defs' body'
     CaseCE inf scr alts -> do
       scr' <- unpackExp scr
       alts' <- mapM unpackAlt alts
       return $ CaseCE inf scr' alts'

-- | Perform unpacking on a value.  If we reach this point, the value isn't
--   going to be used in an unpacked manner.
unpackVal inf value =
  case value
  of ReadVarV addr ptr ->
       case addr
       of Gluon.VarE {Gluon.expVar = a} -> do
            usePacked a
            return $ ValCE inf value
          _ -> internalError "unpackVal: Unexpected address expression"

     -- Other values are not read pass-by-reference, thus ignored by unpacking
     _ -> return $ ValCE inf value

-- | Unpack a function call.
unpackCall :: SynInfo -> RCExp -> [RCExp] -> Maybe RCExp -> U RCExp
unpackCall inf op args mrarg = do
  op' <- unpackExp op
  mrarg' <- mapM unpackExp mrarg
  case op' of
    ValCE _ (OwnedConV op_con)
      | op_con `SF.isPyonBuiltin`
        SF.traverseMember . SF.the_TraversableDict_list ->
          -- Unpack a 'traverse' call
          case args
          of [type_arg, repr_arg,
              ValCE list_inf (ReadVarV list_addr_exp list_ptr)] ->
               case list_addr_exp
               of Gluon.VarE {Gluon.expVar = list_addr} -> 
                    case mrarg
                    of Nothing ->
                         unpackListTraversal inf type_arg repr_arg list_addr
                       _ -> malformed_call
                  _ -> malformed_call
             _ -> malformed_call
    -- Other operators don't get transformed
    _ -> unpackGenericCall inf op' args mrarg'
  where
    malformed_call = internalError "unpackCall: Malformed call"

-- | Unpack a function call that is not transformed at all.
--   The fields of the call are unpacked recursively.
unpackGenericCall inf unpacked_op args unpacked_mrarg = do
  args' <- mapM unpackExp args
  return $ AppCE inf unpacked_op args' unpacked_mrarg

unpackListTraversal inf type_arg repr_arg list_addr = do
  useUnpacked list_addr

  -- Unpack arguments
  type_arg' <- unpackExp type_arg
  repr_arg' <- unpackExp repr_arg
  
  -- Create unpacked list variables
  unpacked_list <- unpackList list_addr
  
  -- Generate code
  let pos = getSourcePos inf
  runGen $ genListTraverse pos list_addr unpacked_list type_arg' repr_arg'

unpackBinder :: CBind LetBinder Rec
             -> U RCExp
             -> U (CBind LetBinder Rec, RCExp)
unpackBinder binder m =
  case binder
  of LocalB a p ::: ty
       | Just elt_ty <- unpackListType ty -> do
           ((), x) <- withListVariable a p elt_ty (nothingAnd m)
           return (binder, x)
       | otherwise -> do
           x <- withOtherVariable a p m
           return (binder, x)
     _ -> do
       -- Not a candidate for unpacking
       x <- m
       return (binder, x)

unpackParam :: CBind CParam Rec -> U (a, RCExp)
            -> U (CBind CParam Rec, (a, RCExp))
unpackParam param m = 
  case param
  of ReadP a p ::: ty
       | Just elt_type <- unpackListType ty -> do
           x <- withListVariable a p elt_type m
           return (param, x)
       | otherwise -> do
           x <- withOtherVariable a p m
           return (param, x)
     _ -> do
       -- Not a candidate for unpacking
       x <- m
       return (param, x)

-- | If the argument is a list type, return its type argument.
--   Otherwise, return Nothing.
unpackListType :: RCType -> Maybe RCType
unpackListType ty =
  case unpackConAppCT ty
  of Just (op, args) 
       | op `SF.isPyonBuiltin` SF.the_list ->
           case args
           of [arg] -> Just arg 
              _ -> internalError "unpackListType"
     _ -> Nothing
     

unpackParams :: [CBind CParam Rec] -> U (a, RCExp) 
             -> U ([CBind CParam Rec], (a, RCExp))
unpackParams params m = do ((params', x), e) <- go params m
                           return (params', (x, e))
  where
    go (p:params) m = do
      (p', ((params', x), e)) <- unpackParam p $ go params m
      return ((p' : params', x), e)
    
    go [] m = do
      (x, e) <- m
      return (([], x), e)
      

unpackAlt :: RCAlt -> U RCAlt
unpackAlt alt = do
  (params', ((), body')) <-
    unpackParams (caltParams alt) (nothingAnd (unpackExp $ caltBody alt))
  return $ alt {caltParams = params', caltBody = body'}

unpackFun :: RCFun -> U RCFun
unpackFun fun = do 
  (params', ((), body')) <- 
    unpackParams (cfunParams fun) (nothingAnd (unpackExp $ cfunBody fun))
  return $ fun { cfunParams = params'
               , cfunEffect = unknown_effect
               , cfunBody = body'}

unpackDef :: CDef Rec -> U (CDef Rec)
unpackDef (CDef v f) = do 
  f' <- unpackFun f
  return (CDef v f')

unpackExport :: CExport Rec -> U (CExport Rec)
unpackExport export = do
  f <- unpackFun (cexportFun export)
  return $ export {cexportFun = f}

-- | Perform the unpacking transformation on all functions defined in a module.
--
-- Traversals of data structures are rewritten to traverse and index into the
-- underlying arrays.
unpackDataStructures :: CModule Rec -> IO (CModule Rec)
unpackDataStructures mod = do
  withTheVarIdentSupply $ \var_supply -> do
    let st = Map.empty
    (_, _, (new_defs, new_exports)) <-
      runU unpack_module_contents var_supply st
    return (mod {cmodDefs = new_defs, cmodExports = new_exports})
  where
    unpack_module_contents = do 
      defs <- mapM (mapM unpackDef) $ cmodDefs mod
      exports <- mapM unpackExport $ cmodExports mod
      return (defs, exports)

-------------------------------------------------------------------------------
-- Code generation

newtype Gen a = Gen (ReaderT (IdentSupply Var) IO a) deriving(Monad)

instance Supplies Gen (Ident Var) where
  fresh = Gen $ ReaderT supplyValue

runGen :: Gen a -> U a
runGen (Gen (ReaderT f)) = U $ \env s -> do
  x <- f env
  return (s, mempty, x)

runGenIO :: IdentSupply Var -> Gen a -> IO a
runGenIO supply (Gen (ReaderT f)) = f supply

-- | Generate an unpacked list traversal expression.
--
-- > generate t pc lsize
-- >   (lambda (i:int) (r:t).
-- >      copy t pc (subscript t pc ldata i) r)
genListTraverse :: SourcePos    -- ^ Location of original code
                -> Var          -- ^ List address
                -> UnpackedList -- ^ Unpacked list variables
                -> RCExp        -- ^ Type parameter
                -> RCExp        -- ^ Repr parameter
                -> Gen RCExp
genListTraverse pos addr ulist type_arg repr_arg = do
  -- Parameter variables for lambda function body
  index_arg <- Gluon.newAnonymousVariable ObjectLevel
  ret_addr <- Gluon.newAnonymousVariable ObjectLevel
  ret_ptr <- Gluon.newAnonymousVariable ObjectLevel
  
  -- Create call to "subscript"
  let subscr_args = [ type_arg
                    , repr_arg
                    , list_data_exp
                    , ValCE inf (ValueVarV index_arg)
                    ]
      subscr_exp = AppCE inf subscr_op subscr_args Nothing
  
  -- Create call to "copy"
  let copy_args = [ type_arg
                  , repr_arg
                  , subscr_exp]
      copy_rarg = ValCE inf $ WriteVarV (Gluon.mkInternalVarE ret_addr) ret_ptr
      copy_exp = AppCE inf copy_op copy_args (Just copy_rarg)
  
  -- Create lambda function
  let fun_params = [ValP index_arg ::: int_type]
      fun_return = WriteR ret_addr ret_ptr ::: elt_type
      function = CFun inf fun_params fun_return unknown_effect copy_exp 
  
  -- Create call to "generate"
  let generate_args = [ ValCE (Gluon.mkSynInfo noSourcePos TypeLevel) (TypeV unknown_effect)
                      , type_arg
                      , repr_arg
                      , list_size_exp
                      , LamCE inf function]
      generate_exp = AppCE inf generate_op generate_args Nothing
  return generate_exp
  where
    inf = Gluon.mkSynInfo pos ObjectLevel
    list_data_exp =
      ValCE inf $
      ReadVarV (Gluon.mkInternalVarE (listDataAddr ulist)) (listDataPtr ulist)
    subscr_op =
      ValCE inf $
      OwnedConV (SF.pyonBuiltin SF.the_fun_subscript)
    copy_op =
      ValCE inf $
      OwnedConV (SF.pyonBuiltin SF.the_fun_copy)
    generate_op =
      ValCE inf $
      OwnedConV (SF.pyonBuiltin SF.the_fun_generate)
    int_type =
      conCT (SF.pyonBuiltin SF.the_int)
    elt_type =
      case type_arg
      of ValCE {cexpVal = TypeV ty} -> ty
         _ -> internalError "genListTraverse: Invalid type argument"
    list_size_exp =
      ValCE inf $ ValueVarV (listSize ulist)

-- | Generate a list unpacking expression.
--
-- > case l
-- > of List t (lsize : int) (ldata : t). exp
genListUnpack :: SourcePos
              -> Var            -- ^ List address
              -> Var            -- ^ List pointer
              -> RCType         -- ^ Type of list elements
              -> UnpackedList   -- ^ Unpacked list variables
              -> RCExp          -- ^ Code that uses unpacked list 
              -> Gen RCExp      -- ^ Code that uses packed list
genListUnpack pos a p elt_type ulist exp = return genlistexpr
  where
    inf = Gluon.mkSynInfo pos ObjectLevel
    int_type = conCT (SF.pyonBuiltin SF.the_int)
    
    -- Unpack the list 
    case_alt =
      let ty_args = [elt_type]
          params = [ ValP (listSize ulist) ::: int_type
                   , ReadP (listDataAddr ulist) (listDataPtr ulist) ::: elt_type]
      in CAlt inf (SF.pyonBuiltin SF.the_makeList) ty_args params exp
    scrutinee = ValCE inf $ ReadVarV (Gluon.mkInternalVarE a) p
    genlistexpr = CaseCE inf scrutinee [case_alt]
  
