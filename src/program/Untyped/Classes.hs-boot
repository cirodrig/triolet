
module Untyped.Classes(pprContext, reduceTypeFunction) where

import Text.PrettyPrint.HughesPJ
import Untyped.Data

reduceTypeFunction :: TyFamily  -- ^ Type function to evaluate
                   -> [HMType]  -- ^ Arguments to the type function
                   -> IO (Maybe HMType) -- ^ Reduced type (if reducible)

pprContext :: [Predicate] -> Ppr Doc