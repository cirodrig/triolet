-- | This module defines a mapping from System F constructors to ANF
-- constructors  

module Pyon.SystemF.Flatten.BuiltinsMap(sfToAnfCon)
where

import qualified Data.IntMap as IntMap
  
import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Core
import qualified Pyon.SystemF.BuiltinsTH as SF
import qualified Pyon.SystemF.Builtins as SF
import qualified Pyon.Anf.Builtins as Anf

-- | Convert a constructor from System F to the corresponding constructor from
-- ANF
sfToAnfCon :: Con -> Con
sfToAnfCon c 
  -- Gluon builtins are unchanged  
  | moduleOf (conName c) == builtinModuleName = c
  -- System F builtins map to ANF builtins
  | moduleOf (conName c) == SF.pyonBuiltinModuleName = lookupAnfCon c
  | otherwise = internalError "sfToAnfCon: Unknown module"

lookupAnfCon :: Con -> Con
lookupAnfCon c =
  let index = fromIdent $ conID c
  in case IntMap.lookup index anfConTable
     of Just c' -> c'
        Nothing -> internalError $ "sfToAnfCon: No translation for System F constructor '" ++ showLabel (conName c) ++ "'"

anfConTable = IntMap.fromList [(fromIdent $ conID $ SF.pyonBuiltin sf_c,
                                Anf.anfBuiltin anf_c)
                              | (sf_c, anf_c) <- assocs]
  where
    assocs =
      [ -- Object types
        (SF.the_NoneType, Anf.the_NoneTypeO)
      , (SF.the_Any, Anf.the_AnyO)
      , (SF.the_bool, Anf.the_boolO)
      , (SF.the_list, Anf.the_listO)
      , (SF.the_Stream, Anf.the_StreamO)
      , (SF.the_AdditiveDict, Anf.the_AdditiveDict)
      , (SF.the_PassConv, Anf.the_PassConv)
        
        -- Data constructors
      , (SF.the_True, Anf.the_TrueV)
      , (SF.the_False, Anf.the_FalseV)
      , (SF.the_additiveDict, Anf.the_additiveDict)  
      ]