
module Untyped.Classes
    (pprContext,
     instantiateClassConstraint,
     andSuperclassEqualityPredicates,
     reduceTypeFunction) where

import Text.PrettyPrint.HughesPJ
import Untyped.Data

instantiateClassConstraint :: ClassSig -> HMType -> IO Constraint

andSuperclassEqualityPredicates :: Predicate -> IO [Predicate]

reduceTypeFunction :: TyFamily  -- ^ Type function to evaluate
                   -> [HMType]  -- ^ Arguments to the type function
                   -> IO (Maybe HMType) -- ^ Reduced type (if reducible)

pprContext :: [Predicate] -> Ppr Doc