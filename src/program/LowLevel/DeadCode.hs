
module LowLevel.DeadCode(eliminateDeadCode)
where

import Prelude hiding(mapM)
import Control.Applicative
import qualified Data.IntMap as IntMap
import Data.Monoid
import Data.Traversable

import Common.Identifier
import LowLevel.Syntax

-- | A map from variable IDs to the number of uses the variable has.
--   If a variable has no uses, it is not in the map.
type UseMap = IntMap.IntMap Uses

v `isUsedIn` m = fromIdent (varID v) `IntMap.member` m

lookupUses v m = case IntMap.lookup (fromIdent (varID v)) m
                 of Nothing -> ZeroUses
                    Just x  -> x

deleteUse v m = IntMap.delete (fromIdent (varID v)) m

deleteUses vs m = foldr deleteUse m vs

useUnion = IntMap.unionWith mappend

useUnions = IntMap.unionsWith mappend

-- | Estimate the size of the code required to define a function,
--   not including the function body.  The size depends on the number of
--   function parameters and returns.
--
--   When computing code size, this component is not accounted to the 
--   function itself, but to the place where the function is defined.
--   It's done this way because this code is not generated for inlined
--   instances of the function.
funDefinitionSize :: Fun -> Int
funDefinitionSize f = length (funParams f) + length (funReturnTypes f) + 1 

data DCEResult a =
  DCEResult
  { size      :: !Int
  , uses      :: UseMap
  , dceResult :: a
  }

type DCE a = a -> DCEResult a

instance Functor DCEResult where
  fmap f x = x {dceResult = f (dceResult x)}

instance Applicative DCEResult where
  pure x  = DCEResult 0 IntMap.empty x
  DCEResult s1 u1 f <*> DCEResult s2 u2 x =
    DCEResult (s1 + s2) (useUnion u1 u2) (f x)

instance Monad DCEResult where
  return = pure
  m >>= k = case m
            of DCEResult s1 u1 x ->
                 case k x
                 of DCEResult s2 u2 y ->
                      DCEResult (s1 + s2) (useUnion u1 u2) y

-- | Add something to the code size
nudge :: Int -> DCEResult a -> DCEResult a
nudge n x = x {size = size x + n}

use :: Var -> DCEResult ()
use v = let use_map = IntMap.singleton (fromIdent $ varID v) OneUse
        in DCEResult 0 use_map ()

-- | Get all observed uses.  Don't propagate uses.
takeUses :: DCEResult a -> DCEResult (UseMap, a)
takeUses (DCEResult s u x) = DCEResult s IntMap.empty (u, x)

putUses :: UseMap -> DCEResult ()
putUses uses = DCEResult 0 uses ()

dceVal :: DCE Val
dceVal value = nudge 1 $
  case value
  of VarV v -> use v *> pure value
     RecV rec vals -> RecV rec <$> dceVals vals
     LitV l -> pure value
     LamV f -> LamV <$> nudge (funDefinitionSize f) (dceFun f)

dceVals :: DCE [Val]
dceVals vs = traverse dceVal vs

-- | Return True if the atom can have an observable side effect in normal
--   program execution, other than producing a result value.
atomHasSideEffect :: Atom -> Bool
atomHasSideEffect atom = 
  case atom
  of ValA {} -> False
     CallA {} -> True
     PrimA prim _ -> primHasSideEffect prim
     PackA {} -> False
     UnpackA {} -> False
     
-- | Return True if an execution of this primitive operation can have an
--   observable side effect in normal program execution, other than 
--   producing a result value or an arithmetic exception.
--
--   Loads have no side effect.  They have no observable effect and don't 
--   fail in normal execution.
primHasSideEffect :: Prim -> Bool
primHasSideEffect prim =
  case prim
  of PrimCastZ {}         -> False
     PrimExtendZ {}       -> False
     PrimAddZ {}          -> False
     PrimSubZ {}          -> False
     PrimMulZ {}          -> False
     PrimModZ {}          -> False
     PrimDivZ {}          -> False
     PrimMaxZ {}          -> False
     PrimMinZ {}          -> False
     PrimCmpZ {}          -> False
     PrimCmpP {}          -> False
     PrimAnd {}           -> False
     PrimOr {}            -> False
     PrimNot {}           -> False
     PrimAddP {}          -> False
     PrimLoad {}          -> False
     PrimStore {}         -> True
     PrimAAddZ {}         -> True
     PrimCastToOwned {}   -> False
     PrimCastFromOwned {} -> False
     PrimGetFrameP {}     -> False
     PrimCastZToF {}      -> False
     PrimCastFToZ {}      -> False
     PrimCmpF {}          -> False
     PrimAddF {}          -> False
     PrimSubF {}          -> False
     PrimMulF {}          -> False
     PrimModF {}          -> False
     PrimDivF {}          -> False
     PrimRoundF {}        -> False
     PrimPowF {}          -> False
     PrimUnaryF {}        -> False

dceAtom :: DCE Atom
dceAtom atom = nudge 1 $
  case atom
  of ValA vs -> ValA <$> dceVals vs
     CallA conv v vs -> CallA conv <$> dceVal v <*> dceVals vs
     PrimA prim vs -> PrimA prim <$> dceVals vs 
     PackA rec vs -> PackA rec <$> dceVals vs
     UnpackA rec v -> UnpackA rec <$> dceVal v

-- | Perform dead code elimination on a statement.
-- 
--   Let and letrec expressions may be removed.
dceStm :: DCE Stm
dceStm statement =
  case statement
  of LetE params rhs body ->
       dceLet params rhs body
     LetrecE defs body ->
       dceLetrec defs body
     SwitchE scrutinee alts ->
       nudge 1 $ SwitchE <$> dceVal scrutinee <*> traverse dceAlt alts
     ReturnE atom ->
       ReturnE <$> dceAtom atom
  where
    dceAlt (x, stm) = (,) x <$> dceStm stm

dceLet params rhs body = do
  (uses, body') <- takeUses $ dceStm body
  putUses $ deleteUses params uses
  if atomHasSideEffect rhs || any (`isUsedIn` uses) params
    then do rhs' <- dceAtom rhs
            return (LetE params rhs' body')
    else return body'

dceLetrec defs body = make_letrec <$> dceDefGroup defs (dceStm body)
  where
    make_letrec (defs', body') 
      | null defs' = body'
      | otherwise = LetrecE defs' body'

dceDefGroup :: [FunDef] -> DCEResult a -> DCEResult ([FunDef], a)
dceDefGroup defs body = do
  -- Compute size and use information
  (filtered_uses, (new_body, annotated_defs)) <-
    takeUses $ (,) <$> body <*> filterFunDefs (uses body) defs
        
  let new_defs = [ rebuildFunDef filtered_uses def result
                 | (def, result) <- annotated_defs]

  -- Expose all uses except the locally defined functions
  putUses $ deleteUses (map definiendum new_defs) filtered_uses

  -- Add code size for the function definitions
  let def_code_size = sum $ map (funDefinitionSize . definiens) new_defs
  nudge def_code_size (return ())
        
  return (new_defs, new_body)

filterFunDefs :: UseMap         -- ^ Uses outside this definition group
              -> [FunDef]       -- ^ Original definitions
              -> DCEResult [(FunDef, Fun)]
filterFunDefs ext_uses defs =
  let dce_funs = map (dceFun . definiens) defs 
      all_uses = useUnions (ext_uses : map uses dce_funs)
  in sequenceA [do {f <- dce_fun; return (def, f)}
               | (def, dce_fun) <- zip defs dce_funs
               , definiendum def `isUsedIn` all_uses]

-- | Rebuild a function definition after DCE.
rebuildFunDef :: UseMap -> FunDef -> Fun -> FunDef 
rebuildFunDef use_map old_def new_fun =
  let fname = definiendum old_def
      fuses = lookupUses fname use_map
      annotated_fun = setFunUses fuses new_fun
  in annotated_fun `seq` Def fname annotated_fun

-- | Perform dead code elimination on a function.  Only the function body 
--   contributes to the code size.
dceFun :: DCE Fun
dceFun fun =
  let DCEResult size uses body = dceStm (funBody fun)
      fun' = setFunSize (codeSize size) $
             mkFun (funConvention fun) (funInlineRequest fun) (funFrameSize fun) (funParams fun) (funReturnTypes fun) body
  in DCEResult size uses fun'

-- | Perform dead code elimination on a data definition.  The data definition
--   is scanned to find out what variables it references.
dceDataDef :: DCE DataDef
dceDataDef (Def v (StaticData rec vals)) =
  (Def v . StaticData rec) <$> dceVals vals

dceTopLevel :: [GlobalDef]      -- ^ Global definitions
            -> [Var]            -- ^ Exported variables
            -> DCEResult [GlobalDef]
dceTopLevel defs exports = do
  let other_uses = use_exports *> dce_data_defs
  
  -- First pass: perform DCE and find all uses
  (filtered_uses, (annotated_fun_defs, new_data_defs)) <-
    takeUses $ (,) <$> filterFunDefs (uses other_uses) fun_defs <*> other_uses

  let new_fun_defs = [ rebuildFunDef filtered_uses def result
                     | (def, result) <- annotated_fun_defs]
  
  -- Don't need to compute uses or code size
  return (map GlobalFunDef new_fun_defs ++ map GlobalDataDef new_data_defs)
  where
    (fun_defs, data_defs) = partitionGlobalDefs defs

    -- All exported variables are used an unknown number of times
    use_exports = 
      putUses $ IntMap.fromList [(fromIdent $ varID v, ManyUses)
                                | v <- exports]

    dce_data_defs = mapM dceDataDef data_defs

-- | Eliminate dead code in a module.
--
--   Also annotate functions with code size and number of uses.
eliminateDeadCode :: Module -> Module
eliminateDeadCode mod@(Module { moduleGlobals = gs
                              , moduleExports = es}) =
  let gs' = dceResult $ dceTopLevel gs (map fst es)
  in mod {moduleGlobals = gs'}