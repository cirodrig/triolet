
module LowLevel.Binary where

import Control.Applicative
import Data.Binary

import Gluon.Common.Error
import Gluon.Common.Identifier
import LowLevel.BinaryUtils
import LowLevel.Label
import LowLevel.Record
import LowLevel.Syntax
import LowLevel.Types

instance Binary ValueType where
  put (PrimType pt) = put pt
  put (RecordType rt) = putWord8 255 >> put rt
  
  get = do tag <- getWord8
           if tag == 255
             then RecordType <$> get
             else PrimType <$> getPrimTypeWithTag tag

instance Binary Uses where
  put = putEnum
  get = getEnum "Uses.get"

instance Binary CodeSize where
  put (CodeSize n) = put n
  get = CodeSize <$> get

instance Binary CmpOp where
  put = putEnum
  get = getEnum "CmpOp.get"

instance Binary Prim where
  put p =
    case p
    of PrimCastZ x y z   -> putWord8 000 >> put x >> put y >> put z
       PrimAddZ x y      -> putWord8 001 >> put x >> put y
       PrimSubZ x y      -> putWord8 002 >> put x >> put y
       PrimMulZ x y      -> putWord8 003 >> put x >> put y
       PrimModZ x y      -> putWord8 004 >> put x >> put y
       PrimMaxZ x y      -> putWord8 005 >> put x >> put y
       PrimCmpZ x y z    -> putWord8 006 >> put x >> put y >> put z
       PrimCmpP x        -> putWord8 007 >> put x
       PrimAnd           -> putWord8 008
       PrimOr            -> putWord8 009
       PrimNot           -> putWord8 010
       PrimAddP          -> putWord8 011
       PrimLoad t        -> putWord8 012 >> put t
       PrimStore t       -> putWord8 013 >> put t
       PrimAAddZ x y     -> putWord8 014 >> put x >> put y
       PrimCastToOwned   -> putWord8 015
       PrimCastFromOwned -> putWord8 016
       PrimCastZToF x y  -> putWord8 017 >> put x >> put y
       PrimCastFToZ x y  -> putWord8 018 >> put x >> put y
       PrimAddF x        -> putWord8 019 >> put x
       PrimSubF x        -> putWord8 020 >> put x
       PrimMulF x        -> putWord8 021 >> put x
       PrimModF x        -> putWord8 022 >> put x
       
  get = getWord8 >>= pick
    where
      pick 000 = PrimCastZ <$> get <*> get <*> get
      pick 001 = PrimAddZ <$> get <*> get
      pick 002 = PrimSubZ <$> get <*> get
      pick 003 = PrimMulZ <$> get <*> get
      pick 004 = PrimModZ <$> get <*> get
      pick 005 = PrimMaxZ <$> get <*> get
      pick 006 = PrimCmpZ <$> get <*> get <*> get
      pick 007 = PrimCmpP <$> get
      pick 008 = pure PrimAnd
      pick 009 = pure PrimOr
      pick 010 = pure PrimNot
      pick 011 = pure PrimAddP
      pick 012 = PrimLoad <$> get
      pick 013 = PrimStore <$> get
      pick 014 = PrimAAddZ <$> get <*> get
      pick 015 = pure PrimCastToOwned
      pick 016 = pure PrimCastFromOwned
      pick 017 = PrimCastZToF <$> get <*> get
      pick 018 = PrimCastFToZ <$> get <*> get
      pick 019 = PrimAddF <$> get
      pick 020 = PrimSubF <$> get
      pick 021 = PrimMulF <$> get
      pick 022 = PrimModF <$> get
      pick _ = readError "Prim.get"

instance Binary Lit where
  put UnitL = putWord8 0
  put NullL = putWord8 1
  put (BoolL True) = putWord8 2
  put (BoolL False) = putWord8 3
  put (IntL x y n) = putWord8 4 >> put x >> put y >> put n
  put (FloatL x n) = putWord8 5 >> put x >> put n
  get = getWord8 >>= pick
    where
      pick 0 = pure UnitL
      pick 1 = pure NullL
      pick 2 = pure (BoolL True)
      pick 3 = pure (BoolL False)
      pick 4 = IntL <$> get <*> get <*> get
      pick 5 = FloatL <$> get <*> get
      pick _ = readError "Lit.get"

instance Binary ModuleName where
  put mn = put (showModuleName mn)
  get = moduleName <$> get

instance Binary LabelTag where
  put = putEnum
  get = getEnum "LabelTag.get"

instance Binary Label where
  put (Label mod lnm tag xnm) = put mod >> put lnm >> put tag >> put xnm
  get = Label <$> get <*> get <*> get <*> get

instance Binary Var where
  put (Var n x nm ty) = put (fromIdent n) >> put x >> put nm >> put ty
  get = Var <$> fmap toIdent get <*> get <*> get <*> get

instance Binary Val where
  put (VarV v)     = putWord8 0 >> put v
  put (RecV sr vs) = putWord8 1 >> put sr >> put vs
  put (LitV l)     = putWord8 2 >> put l
  put (LamV f)     = putWord8 3 >> put f
  get = getWord8 >>= pick
    where
      pick 0 = VarV <$> get
      pick 1 = RecV <$> get <*> get
      pick 2 = LitV <$> get
      pick 3 = LamV <$> get

instance Binary CallConvention where
  put = putEnum
  get = getEnum "CallConvention.get"

instance Binary Atom where
  put (ValA vs)          = putWord8 0 >> put vs
  put (CallA cc op args) = putWord8 1 >> put cc >> put op >> put args
  put (PrimA prim args)  = putWord8 2 >> put prim >> put args
  put (PackA sr args)    = putWord8 3 >> put sr >> put args
  put (UnpackA sr arg)   = putWord8 4 >> put sr >> put arg
  get = getWord8 >>= pick
    where
      pick 0 = ValA <$> get
      pick 1 = CallA <$> get <*> get <*> get
      pick 2 = PrimA <$> get <*> get
      pick 3 = PackA <$> get <*> get      
      pick 4 = UnpackA <$> get <*> get

instance Binary Stm where
  put (LetE params rhs body) = putWord8 0 >> put params >> put rhs >> put body
  put (LetrecE defs body) = putWord8 1 >> put defs >> put body 
  put (SwitchE s a) = putWord8 2 >> put s >> put a
  put (ReturnE a) = putWord8 3 >> put a
  get = getWord8 >>= pick
    where
      pick 0 = LetE <$> get <*> get <*> get
      pick 1 = LetrecE <$> get <*> get
      pick 2 = SwitchE <$> get <*> get
      pick 3 = ReturnE <$> get

instance Binary Fun where
  put f = do
    put $ funConvention f
    put $ funSize f
    put $ funUses f
    put $ funParams f
    put $ funReturnTypes f
    put $ funBody f
  get = do
    cc <- get
    size <- get
    uses <- get
    params <- get
    return_types <- get
    body <- get
    return $ Fun { funConvention = cc
                 , funSize = size
                 , funUses = uses
                 , funParams = params
                 , funReturnTypes = return_types
                 , funBody = body}

instance Binary StaticData where
  put (StaticData r v) = put r >> put v
  get = StaticData <$> get <*> get

instance (Binary a) => Binary (Def a) where
  put (Def v x) = put v >> put x
  get = Def <$> get <*> get

instance Binary GlobalDef where
  put (GlobalFunDef d) = putWord8 0 >> put d
  put (GlobalDataDef d) = putWord8 1 >> put d
  get = do tag <- getWord8
           case tag of
             0 -> GlobalFunDef <$> get
             1 -> GlobalDataDef <$> get
