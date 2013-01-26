
module Untyped.Variable where

import Data.Function
import System.IO.Unsafe
import Text.PrettyPrint.HughesPJ

import Common.Identifier
import Common.Label
import Common.Supply
import qualified Type.Var as SF

data Variable =
  Variable 
  { varID :: {-# UNPACK #-} !(Ident Variable)
  , varName :: !(Maybe Label)
    -- | If this variable corresponds to a variable in System F, this is the 
    -- System F variable.  Otherwise, this is Nothing.
  , varSystemFVariable :: !(Maybe SF.Var)
  }

instance Eq Variable where
  (==) = (==) `on` varID

instance Ord Variable where
  compare = compare `on` varID

variableIDSupply :: Supply (Ident Variable)
{-# NOINLINE variableIDSupply #-}
variableIDSupply = unsafePerformIO newIdentSupply

getNextVariableID :: IO (Ident Variable)
getNextVariableID = supplyValue variableIDSupply

newVariable :: Maybe Label -> Maybe SF.Var -> IO Variable
newVariable lab sf = do
  id <- getNextVariableID
  return $ Variable id lab sf

pprVariable :: Variable -> Doc
pprVariable v =
  let name = maybe "_" showLabel $ varName v 
      num  = show $ fromIdent $ varID v
  in text $ name ++ "'" ++ num

showVariable v = show (pprVariable v)