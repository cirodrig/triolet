{-| Correctness checks for low-level code, used for debugging. 
-}
module LowLevel.Lint
       (checkFunEntryPoints, checkDuplicateGlobalDefinitions)
where

import Common.Error
import Data.List
import Data.Monoid
import qualified Data.Set as Set
import LowLevel.CodeTypes
import LowLevel.Syntax

-- | Verify the consistency of a function's 'EntryPoints'
checkFunEntryPoints :: Fun -> ()
checkFunEntryPoints f =
  case funEntryPoints f
  of Nothing -> ()
     Just ep
       | funType f /= entryPointsType ep ->
           internalError "checkFunEntryPoints"
       | otherwise -> ()

-------------------------------------------------------------------------------

-- | Find duplicate definitions.
--   Keep track of all unique definitions and all duplicate definitions
--   separately.
data FDD = FDD {unique, duplicate :: Set.Set Var}

fddMember :: Var -> FDD -> Bool
v `fddMember` (FDD u d) = v `Set.member` u || v `Set.member` d

instance Monoid FDD where
  mempty = FDD Set.empty Set.empty
  x `mappend` y =
    let (new_duplicate_x, unique_x) = Set.partition (`fddMember` y) $ unique x
        (new_duplicate_y, unique_y) = Set.partition (`fddMember` x) $ unique y
        dup = Set.unions [duplicate x, new_duplicate_x,
                          duplicate y, new_duplicate_y]
    in FDD (Set.union unique_x unique_y) dup

entryPointsFDD :: EntryPoints -> FDD
entryPointsFDD ep = FDD (Set.fromList $ entryPointsVars ep) Set.empty

def :: Var -> FDD
def v = FDD (Set.singleton v) Set.empty

-- | Get the variables defined by an import
importDefinitions :: Import -> FDD
importDefinitions (ImportClosureFun ep _) = entryPointsFDD ep
importDefinitions (ImportPrimFun v _ _) = def v
importDefinitions (ImportData v _) = def v

globalDefinitions :: GlobalDef -> FDD
globalDefinitions (GlobalFunDef (Def v f)) =
  case funEntryPoints f
  of Nothing -> def v
     Just ep -> entryPointsFDD ep

globalDefinitions (GlobalDataDef (Def v _)) = def v

findDuplicateGlobalDefinitions :: Module -> Set.Set Var
findDuplicateGlobalDefinitions mod =
  let import_defs = mconcat $ map importDefinitions $ moduleImports mod
      global_defs = mconcat [ globalDefinitions d
                            | group <- moduleGlobals mod,
                              d <- groupMembers group]
      defs = mappend import_defs global_defs
  in duplicate defs

-- | Throw an error if any global variables are multiply defined in the module
checkDuplicateGlobalDefinitions :: Module -> ()
checkDuplicateGlobalDefinitions mod =
  let s = findDuplicateGlobalDefinitions mod
      text = intercalate " " $ map show $ Set.elems s
  in if Set.null s
     then ()
     else internalError $ "Multiply defined globals:" ++ text