{-| Information about how a function is closure converted.
-}

module LowLevel.Closure.CCInfo where

import Control.Monad
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import LowLevel.Build
import LowLevel.Records
import LowLevel.FreshVar
import LowLevel.CodeTypes
import LowLevel.Print
import LowLevel.Syntax
import LowLevel.Closure.LocalCPSAnn

-- | Get the type of a variable; it must be a primitive type.
varPrimType :: Var -> PrimType
varPrimType v = valueToPrimType (varType v)

-- | Get the type of a value.  Since record flattening has been performed, 
-- the type must be a primitive type.
valPrimType :: Val -> PrimType
valPrimType val =
  case valType val 
  of PrimType pt -> pt
     RecordType _ -> internalError "valPrimType"

-- | Create an immutable record to hold the given closure-captured variables.
--   The variables' types are promoted.
variablesRecord :: [Var] -> StaticRecord
variablesRecord vals =
  constStaticRecord $ map (PrimField . promoteType . varPrimType) vals

-- | Create a record that can hold values of the given types after type
--   promotion.
promotedPrimTypesRecord :: Mutability -> [PrimType] -> StaticRecord
promotedPrimTypesRecord mut tys =
  staticRecord [(mut, PrimField $ promoteType t) | t <- tys]

-- | Create a record representing arguments of a PAP.
--   The record's fields are promoted, then padded to a multiple of
--   'dynamicScalarAlignment'.
papArgsRecord :: Mutability -> [PrimType] -> StaticRecord
papArgsRecord mut tys =
  staticRecord $ concatMap mk_field tys
  where
    mk_field ty =
      let pty = promoteType ty
      in [(Constant, AlignField dynamicScalarAlignment), (mut, PrimField pty)]

-------------------------------------------------------------------------------

-- | The strategy for closure-converting a function.
--
--   This data structure records everything needed to closure-convert a function
--   or to call a closure-converted function, except the function body.
--
--   There are two kinds of captured variables.
--
--   * /call-captured/ variables are converted to normal function
--   parameters.  They are applied to a function each time the
--   function is directly referenced in the program, regardless of
--   whether it is a saturated call or not.  
--
--   * /closure-captured/ variables are added to a function closure
--   at the time the closure is created.  The closure holds promoted 
--   data types, so the types of the closure-captured variables may not 
--   match the field types of the closure-captured record.
data CCInfo =
    -- | A global function that can be used as a first-class value
    GlobalClosure
    { _cEntryPoints :: EntryPoints
    }
    -- | A local function that is hoisted to the top level
  | LocalClosure
    { _cEntryPoints :: EntryPoints
    , _cRecord :: StaticRecord
    , _cCallCaptured :: [Var]
    , _cClosureCaptured :: [Var]
    , _cClosureCapturedRecord :: StaticRecord
    , _cWantClosure :: !Bool
    }
    -- | A global function that must be direct-called
  | GlobalPrim
    { _cType :: FunctionType
    }
    -- | A local function that must be direct tail-called.
    --   The function may have originally been a closure-call or join-call
    --   function.
    --
    --   The closure-converted entry point is saved here.  If it was
    --   originally a join-call function, it's the same as the original entry 
    --   point; otherwise it's a new variable. 
    --   Creating a new variable is necessary because the variable's type
    --   changed in the conversion process.
  | LocalPrim
    { _cType :: FunctionType
    , _cEntryPoint :: Var
    , _cCallCaptured :: [Var]
    }

pprCCInfo :: CCInfo -> Doc
pprCCInfo (GlobalClosure {}) =
  text "GlobalClosure"

pprCCInfo (LocalClosure {_cCallCaptured = call, _cClosureCaptured = closure}) =
  hang (text "LocalClosure") 4 (text (show call) $$ text (show closure))

pprCCInfo (GlobalPrim {}) =
  text "GlobalPrim"

pprCCInfo (LocalPrim {_cCallCaptured = call}) =
  hang (text "LocalPrim") 4 (text $ show call)

-- | Closure conversion uses a lookup table to find CCInfo for a function
type CCInfos = Map.Map Var CCInfo

-- | Get the type that a function has before closure conversion
ccType :: CCInfo -> FunctionType
ccType (GlobalClosure {_cEntryPoints = ep}) = entryPointsType ep
ccType (LocalClosure {_cEntryPoints = ep})  = entryPointsType ep
ccType (GlobalPrim {_cType = ft})           = ft
ccType (LocalPrim {_cType = ft})            = ft

ccIsHoisted :: CCInfo -> Bool
ccIsHoisted (LocalClosure {})  = True
ccIsHoisted (GlobalClosure {}) = False
ccIsHoisted (GlobalPrim {})    = False
ccIsHoisted (LocalPrim {})     = False

-- | Determine whether static or dynamic closures will be created for
--   the function after closure-conversion.
ccIsClosure :: CCInfo -> Bool
ccIsClosure (LocalClosure {})  = True
ccIsClosure (GlobalClosure {}) = True
ccIsClosure (GlobalPrim {})    = False
ccIsClosure (LocalPrim {})     = False

ccIsGlobalPrim (GlobalPrim {}) = True
ccIsGlobalPrim _ = False

ccIsGlobalClosure (GlobalClosure {}) = True
ccIsGlobalClosure _ = False

-- | Get the direct entry point of a local function or procedure.  
ccJumpTarget :: CCInfo -> Var
ccJumpTarget (LocalClosure {_cEntryPoints = ep}) = directEntry ep
ccJumpTarget (LocalPrim {_cEntryPoint = ep}) = ep
ccJumpTarget _ = internalError "ccDirectEntry: Not a local function or procedure"

ccEntryPoints cc = _cEntryPoints cc

ccArity cc = length $ ftParamTypes $ ccType cc

-- | Should a closure be constructed for this variable?
--
--   It only makes sense to test this for closure-call functions.
ccWantClosure (GlobalClosure {}) = True
ccWantClosure (LocalClosure {_cWantClosure = b}) = b
ccWantClosure _ = internalError "ccWantClosure"

-- | Get the variables captured by a function at closure definition time
ccClosureCaptured :: CCInfo -> [Var]
ccClosureCaptured (GlobalClosure {}) = []
ccClosureCaptured (LocalClosure {_cClosureCaptured = xs}) = xs
ccClosureCaptured (GlobalPrim {}) = []
ccClosureCaptured (LocalPrim {}) = []

-- | Get the variables captured by a function when the function is referenced
ccCallCaptured :: CCInfo -> [Var]
ccCallCaptured (GlobalClosure {}) = []
ccCallCaptured (LocalClosure {_cCallCaptured = xs}) = xs
ccCallCaptured (GlobalPrim {}) = []
ccCallCaptured (LocalPrim {_cCallCaptured = xs}) = xs

-- | Get the set of all variables captured by a function.
--
--   Order matters: the call-captured variables come last because that is the
--   order that they are passed to the direct entry point.
ccCaptured :: CCInfo -> [Var]
ccCaptured cc = ccClosureCaptured cc ++ ccCallCaptured cc

-- | Get the parameter types of the direct entry point.
--   These consist of closure-captured variables, call-captured variables,
--   and the original function parameters, in that order.
ccDirectParamTypes :: CCInfo -> [ValueType]
ccDirectParamTypes cc =
  map varType (ccCaptured cc) ++ ftParamTypes (ccType cc)

-- | Get the parameters of the exact entry point, excluding the closure pointer.
--   These consist of the call-captured variables
--   and the original function parameters, in that order.
ccExactParamTypes :: CCInfo -> [ValueType]
ccExactParamTypes cc =
  map varType (ccCallCaptured cc) ++ -- Call-captured
  ftParamTypes (ccType cc)           -- Original parameters

-- | Create a 'CCInfo' for a global variable definition.
--   If it's a closure-call variable, a 'GlobalClosure' is created;
--   otherwise a 'GlobalPrim' is created.
globalCCInfo :: FunDef -> FreshVarM CCInfo
globalCCInfo (Def v f) =
  case funConvention f
  of ClosureCall -> do
       ep <- case varName v
             of Just name -> mkGlobalEntryPoints (funType f) name v
                Nothing -> mkEntryPoints False (funType f) v
       return $ GlobalClosure ep
     PrimCall -> do
       return $ GlobalPrim (funType f)
     JoinCall ->
       internalError "globalCCInfo: Global function is a join point"

-- | Create a 'CCInfo' for an imported symbol,
--   if the symbol is a function or procedure.
importCCInfo :: Import -> FreshVarM (Maybe CCInfo)
importCCInfo (ImportClosureFun ep _) = return $ Just $ GlobalClosure ep
importCCInfo (ImportPrimFun _ ty _)  = return $ Just $ GlobalPrim ty
importCCInfo (ImportData {})         = return Nothing

importCCInfos :: [Import] -> FreshVarM CCInfos
importCCInfos imps = foldM go Map.empty imps
  where
    go m im = do
      m_cc <- importCCInfo im
      return $! case m_cc
                of Nothing -> m
                   Just cc -> Map.insert (importVar im) cc m

-- | Create an entry point for a local function or procedure.
--
--   A procedure translates to a procedure, so we can reuse the variable name.
--   A function is translated to a procedure, so create a new name.
mkLocalEntryPointName :: CallConvention -> Var -> FreshVarM Var
mkLocalEntryPointName JoinCall v =
  return v

mkLocalEntryPointName ClosureCall v =
  newVar (varName v) (PrimType PointerType)

mkLocalEntryPointName PrimCall _ =
  internalError "mkLocalEntryPointName: Local function is a procedure"

-- | Analysis results regarding a single function.  These results are used for
-- constructing a 'CCInfo'.
data FunAnalysisResults =
  FunAnalysisResults
  { -- | Whether the function will be hoisted
    funHoisted :: !Bool
    -- | Whether the function (if hoisted) needs a closure record and
    --   indirect entry point
  , funBuildsClosure :: !Bool
    -- | The set of local variables used by the function but not defined in
    --   the function
  , funCaptured :: Set.Set Var
  }

-- | A list of local variables that are in scope at some program point.
type LocalsInScope = [Var]

-------------------------------------------------------------------------------

groupCCInfo :: (Var -> FunAnalysisResults) -- ^ Hoisting and capture information
            -> [Var]                       -- ^ The variables defined in this group
            -> Set.Set Var                  -- ^ The in-scope local variables
            -> Group FunDef                 -- ^ The definition group
            -> FreshVarM [(Var, CCInfo)]
groupCCInfo get_capture defined_here in_scope_set (Rec grp_members) =
  let capture_info = do
        member <- grp_members
        let v = definiendum member
            conv = funConvention $ definiens member
            ftype = funType $ definiens member
            FunAnalysisResults hoisted closure captured = get_capture v
        return (hoisted, (v, conv, ftype, closure, captured))

      -- Find the hoisted and unhoisted functions in the group
      hoisted   :: [(Var, CallConvention, FunctionType, Bool, Set.Set Var)]
      unhoisted :: [(Var, CallConvention, FunctionType, Bool, Set.Set Var)]
      (hoisted, unhoisted) = partition_h [] [] capture_info
        where
          partition_h h u ((True,  x):xs) = partition_h (x : h) u xs
          partition_h h u ((False, x):xs) = partition_h h (x : u) xs
          partition_h h u []              = (reverse h, reverse u)

      definienda = map definiendum grp_members

      -- Identify the captured variable set, which is a subset of the
      -- variables in scope at the defgroup.
      shared_set = in_scope_set `Set.intersection`
                   Set.unions [s | (_, _, _, _, s) <- hoisted ++ unhoisted]
      shared_list = Set.toList shared_set
      shared_record = variablesRecord shared_list
      closure_record = localClosureRecord shared_record
      
      create_hoisted_closure (v, call_conv, ftype, want_closure, captured_set) = do
        let call_captured = Set.toList (captured_set Set.\\ shared_set)
        entry_points <-
          case call_conv
          of ClosureCall -> mkEntryPoints False ftype v
             JoinCall -> do
               -- This function has the wrong type, so create a new variable
               v' <- newVar (varName v) (PrimType OwnedType)
               let ftype' = closureFunctionType (ftParamTypes ftype) (ftReturnTypes ftype)
               mkEntryPoints False ftype' v'
               
        return (v, LocalClosure entry_points closure_record call_captured
                   shared_list shared_record want_closure)

      create_unhoisted_closure (v, conv, ftype, _, captured_set) = do
        let call_captured_set1 = captured_set Set.\\ shared_set
            -- Don't capture the definition group members
            call_captured_set2 = foldr Set.delete call_captured_set1 defined_here
            call_captured = Set.toList call_captured_set2
        entry_point <- mkLocalEntryPointName conv v
        return (v, LocalPrim ftype entry_point call_captured)

  in do h <- mapM create_hoisted_closure hoisted
        u <- mapM create_unhoisted_closure unhoisted
        return (h ++ u)

-- | Extract closure conversion information from all function definitions 
--   in a statement.
--
--   Ignore the 'funGroup' field of 'FunAnalysisResults'.  It used to be
--   used, but we no longer need it.
stmCCInfo :: (Var -> FunAnalysisResults)
          -> Set.Set Var
          -> Stm
          -> FreshVarM [(Var, CCInfo)]
stmCCInfo cc_stats in_scope stm =
  case stm
  of LetE params _ body ->
       continue (extend_scope in_scope params) body
     LetrecE g body -> do
       -- Add the local variables to the set of in-scope variables
       let local_fun_vars = case g of Rec defs -> map definiendum defs
           local_vars = extend_scope in_scope local_fun_vars

       -- Compute CCInfo for this group, function bodies in this group, and
       -- the letrec body
       xs1 <- groupCCInfo cc_stats local_fun_vars local_vars g

       -- Each function brings its call-captured variables and parameters
       -- into scope.
       xss2 <- forM (groupMembers g) $ \def ->
         let Just cc = lookup (definiendum def) xs1 
             call_captured = ccCallCaptured cc
             fun_params = funParams $ definiens def
             body_scope = extend_scope local_vars (call_captured ++ fun_params)
         in continue body_scope $ funBody $ definiens def

       xs3 <- continue local_vars body
       return (xs1 ++ concat xss2 ++ xs3)
     SwitchE _ alts -> do
       xs <- sequence [continue in_scope s | (_, s) <- alts]
       return $ concat xs
     ReturnE _ -> return []
     ThrowE _ -> return []
  where
    extend_scope scope vs = foldr Set.insert scope vs
    continue local_vars stm = stmCCInfo cc_stats local_vars stm