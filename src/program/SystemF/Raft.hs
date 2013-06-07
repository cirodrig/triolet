{-| Rafts are a data structure used when restructuring expressions into
    simpler forms that are easier to optimize.  They are a special case
    of \"contexts\", or expressions with one hole
    to be filled in by additional code.  

    Like expressions, rafts include variable references and bindings.  
    Code that uses rafts must properly keep track of in-scope variables.
-}

module SystemF.Raft
       (Raft(..),
        RaftAlt(..),
        exceptingAltRaft,
        normalAltRaft,
        applyRaft,
        partitionRaft,
        assumeRaft)
where

import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set

import SystemF.Rename
import SystemF.Syntax
import SystemF.MemoryIR
import Type.Rename
import Type.Type
import Type.Environment

data Raft =
    -- | The hole
    Here

    -- | A let binding
  | LetR
    { raftInfo :: ExpInfo 
    , raftBinder :: PatM 
    , raftValue :: ExpM 
    , raftBody :: Raft
    }

    -- | A letrec binding
  | LetfunR 
    { raftInfo :: ExpInfo
    , raftDefs :: DefGroup (FDef Mem)
    , raftBody :: Raft
    }

    -- | A case analysis with exactly one non-excepting matching alternative
  | Case1R 
    { raftInfo              :: ExpInfo
    , raftScrutinee         :: ExpM
    , raftSizeParams        :: [ExpM]
    , raftBranch            :: RaftAlt Raft
    , raftExceptingBranches :: [RaftAlt ()]
    }

data RaftAlt e = RaftAlt !DeConInst !(Maybe PatM) [PatM] e

instance Functor RaftAlt where
  fmap f (RaftAlt dc p ps x) = RaftAlt dc p ps (f x)

-- | Rafts form a monoid.  @x `mappend` y@ nests @y@ inside @x@.
instance Monoid Raft where
  mempty = Here
  mappend = fillHole

-- | Put 'y' into the hole of 'x'
fillHole :: Raft -> Raft -> Raft
fillHole raft x =
  case raft
  of Here                       -> x
     LetR {raftBody = raft'}    -> raft {raftBody = fillHole raft' x}
     LetfunR {raftBody = raft'} -> raft {raftBody = fillHole raft' x}
     Case1R {raftBranch = br}   -> raft {raftBranch = fill_branch br x}
  where
    fill_branch (RaftAlt decon tyob_param params body) x =
      RaftAlt decon tyob_param params (fillHole body x)

exceptingAltRaft :: AltM -> RaftAlt ()
exceptingAltRaft (AltM (Alt inf tyob params _)) = RaftAlt inf tyob params ()

normalAltRaft :: AltM -> RaftAlt Raft
normalAltRaft (AltM (Alt inf tyob params _)) = RaftAlt inf tyob params Here

applyRaft :: Raft -> Type -> ExpM -> ExpM
applyRaft Here _ e = e

applyRaft (LetR inf b rhs body) t e =
  ExpM $ LetE inf b rhs (applyRaft body t e)

applyRaft (LetfunR inf defgroup body) t e =
  ExpM $ LetfunE inf defgroup (applyRaft body t e)

applyRaft (Case1R inf scr sps br exc_brs) t e =
  let taken_branch = applyRaftAlt br t e
      excepting_branches = [applyRaftAlt (fmap (const Here) ebr) t exception
                           | ebr <- exc_brs]
        where
          exception = ExpM $ ExceptE inf t
  in ExpM $ CaseE inf scr sps (taken_branch : excepting_branches)

applyRaftAlt :: RaftAlt Raft -> Type -> ExpM -> AltM
applyRaftAlt (RaftAlt decon tyob_param params body) t e =
  AltM $ Alt decon tyob_param params (applyRaft body t e)

-- | Split a raft into those parts that depend on the given variables
--   and those parts that do not.
partitionRaft :: Set.Set Var -> Raft -> (Raft, Raft)
partitionRaft dependences raft = extendPartition dependences Here Here raft

extendPartition (!dependences) dependent independent raft =
  case raft
  of Here ->
       (dependent, independent)

     LetR inf b rhs body ->
       let fv = binderFreeVariables (patMBinder b) Set.empty `Set.union`
                freeVariables rhs
       in add_if_dependent fv [patMVar b] (LetR inf b rhs Here) body

     LetfunR inf group body ->
       let fv = defGroupFreeVariables group Set.empty
           bv = map definiendum $ defGroupMembers group
       in add_if_dependent fv bv (LetfunR inf group Here) body

     Case1R inf scr sps alt@(RaftAlt decon tyob_param params body) exc_brs ->
       let fv = Set.unions $ [freeVariables scr, freeVariables sps,
                              altFreeVariables $ fmap (const ()) alt] ++
                             map altFreeVariables exc_brs
           bv = map binderVar (deConExTypes decon) ++
                maybeToList (fmap patMVar tyob_param) ++
                map patMVar params
       in add_if_dependent fv bv (Case1R inf scr sps (RaftAlt decon tyob_param params Here) exc_brs) body
  where
    -- Check the free variables to decide whether this part of the raft
    -- is dependent on the give nset of variables.  Add it to one of the
    -- two rafts accordingly.
    add_if_dependent free_vars bound_vars this_raft remainder =
      if Set.null $ free_vars `Set.intersection` dependences
      then add_to_independent bound_vars this_raft remainder
      else add_to_dependent bound_vars this_raft remainder

    add_to_independent bound_vars this_raft remainder =
      let dependences' = foldr Set.delete dependences bound_vars
          independent' = independent `mappend` this_raft
      in extendPartition dependences' dependent independent' remainder

    add_to_dependent bound_vars this_raft remainder =
      let dependences' = foldr Set.insert dependences bound_vars
          dependent' = dependent `mappend` this_raft
      in extendPartition dependences' dependent' independent remainder

altFreeVariables :: RaftAlt () -> Set.Set Var
altFreeVariables (RaftAlt decon tyob_param params body) =
  let params_fv =
        bindersFreeVariables
        (map patMBinder $ maybeToList tyob_param ++ params) Set.empty
  in deConFreeVariables decon params_fv

-- | Add a raft's bound variables to the environment
assumeRaft :: TypeEnvMonad m => Raft -> m a -> m a
assumeRaft raft m = undefined