
module SystemF.Rename where

import SystemF.Syntax
import Type.Rename

instance Renameable Dmd
instance Renameable Specificity

renameHeapMap :: Renameable a => Renaming -> HeapMap a -> HeapMap a