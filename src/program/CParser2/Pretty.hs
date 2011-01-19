
module CParser2.Pretty where

import Text.PrettyPrint.HughesPJ

class Pretty a where ppr :: a -> Doc