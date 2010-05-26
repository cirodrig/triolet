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
      , (SF.the_int, Anf.the_intO)
      , (SF.the_float, Anf.the_floatO)
      , (SF.the_list, Anf.the_listO)
      , (SF.the_Stream, Anf.the_StreamO)
      , (\_ -> SF.getPyonTupleType' 0, Anf.the_PyonTuple0O)
      , (\_ -> SF.getPyonTupleType' 1, Anf.the_PyonTuple1O)
      , (\_ -> SF.getPyonTupleType' 2, Anf.the_PyonTuple2O)
      , (SF.the_EqDict, Anf.the_EqDict)
      , (SF.the_OrdDict, Anf.the_OrdDict)
      , (SF.the_AdditiveDict, Anf.the_AdditiveDict)
      , (SF.the_PassConv, Anf.the_PassConv)
        
        -- Data constructors
      , (SF.the_True, Anf.the_TrueV)
      , (SF.the_False, Anf.the_FalseV)
      , (SF.the_eqDict, Anf.the_eqDict)
      , (SF.the_ordDict, Anf.the_ordDict)
      , (SF.the_additiveDict, Anf.the_additiveDict)
        
        -- Introduction functions
      , (\_ -> SF.getPyonTupleCon' 2, Anf.the_intro_PyonTuple2)
        
        -- Constants
      , (SF.the_passConv_float, Anf.the_passConv_float)
      , (SF.the_passConv_int, Anf.the_passConv_int)
        
        -- Functions
      , (SF.eqMember . SF.the_EqDict_int, Anf.the_Eq_EQ_int)
      , (SF.neMember . SF.the_EqDict_int, Anf.the_Eq_NE_int)
      , (SF.eqMember . SF.the_EqDict_float, Anf.the_Eq_EQ_float)
      , (SF.neMember . SF.the_EqDict_float, Anf.the_Eq_NE_float)
      , (SF.gtMember . SF.the_OrdDict_int, Anf.the_Ord_GT_int)
      , (SF.geMember . SF.the_OrdDict_int, Anf.the_Ord_GE_int)
      , (SF.ltMember . SF.the_OrdDict_int, Anf.the_Ord_LT_int)
      , (SF.leMember . SF.the_OrdDict_int, Anf.the_Ord_LE_int)
      , (SF.gtMember . SF.the_OrdDict_float, Anf.the_Ord_GT_float)
      , (SF.geMember . SF.the_OrdDict_float, Anf.the_Ord_GE_float)
      , (SF.ltMember . SF.the_OrdDict_float, Anf.the_Ord_LT_float)
      , (SF.leMember . SF.the_OrdDict_float, Anf.the_Ord_LE_float)
      , (SF.zeroMember . SF.the_AdditiveDict_int, Anf.the_Additive_ZERO_int)
      , (SF.addMember . SF.the_AdditiveDict_int, Anf.the_Additive_ADD_int)
      , (SF.subMember . SF.the_AdditiveDict_int, Anf.the_Additive_SUB_int)
      , (SF.zeroMember . SF.the_AdditiveDict_float, Anf.the_Additive_ZERO_float)
      , (SF.addMember . SF.the_AdditiveDict_float, Anf.the_Additive_ADD_float)
      , (SF.subMember . SF.the_AdditiveDict_float, Anf.the_Additive_SUB_float)
        
      , (SF.the_oper_DIV, Anf.the_oper_DIV)
      , (SF.the_oper_MOD, Anf.the_oper_MOD)
      , (SF.the_oper_FLOORDIV, Anf.the_oper_FLOORDIV)
      , (SF.the_oper_POWER, Anf.the_oper_POWER)
      , (SF.the_oper_NEGATE, Anf.the_oper_NEGATE)
      , (SF.the_oper_BITWISEAND, Anf.the_oper_BITWISEAND)
      , (SF.the_oper_BITWISEOR, Anf.the_oper_BITWISEOR)
      , (SF.the_oper_BITWISEXOR, Anf.the_oper_BITWISEXOR)
      ]