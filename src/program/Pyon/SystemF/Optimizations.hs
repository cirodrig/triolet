
module Pyon.SystemF.Optimizations
    (optimizeModule)
where

import qualified Gluon.Core as Gluon
import Pyon.SystemF.Syntax

-- | Apply optimizations to a module.
optimizeModule :: Module -> Module
optimizeModule mod = mod