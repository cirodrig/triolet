
module Common.Error where

internalError :: String -> a
internalError msg = error $ "Internal error:\n" ++ msg