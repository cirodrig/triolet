
{-# OPTIONS -fwarn-incomplete-patterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
module LowLevel.Binary where

import Control.Applicative
import Control.Monad
import Data.Binary

import Common.Error
import Common.Identifier
import Common.Label
import LowLevel.BinaryUtils
import LowLevel.Syntax
import LowLevel.CodeTypes

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

instance Binary RoundMode where
  put = putEnum
  get = getEnum "RoundMode.get"

instance Binary UnaryFPIntrinsic where
  put = putEnum
  get = getEnum "UnaryFPIntrinsic.get"

instance Binary PointerKind where
  put = putEnum
  get = getEnum "PointerKind.get"

instance Binary Prim where
  put p =
    case p
    of PrimCastZ x y z   -> putWord8 000 >> put x >> put y >> put z
       PrimExtendZ x y z -> putWord8 001 >> put x >> put y >> put z
       PrimAddZ x y      -> putWord8 002 >> put x >> put y
       PrimSubZ x y      -> putWord8 003 >> put x >> put y
       PrimMulZ x y      -> putWord8 004 >> put x >> put y
       PrimModZ x y      -> putWord8 005 >> put x >> put y
       PrimDivZ x y      -> putWord8 006 >> put x >> put y
       PrimMaxZ x y      -> putWord8 007 >> put x >> put y
       PrimMinZ x y      -> putWord8 008 >> put x >> put y
       PrimCmpZ x y z    -> putWord8 009 >> put x >> put y >> put z
       PrimCmpP x        -> putWord8 010 >> put x
       PrimSelect t      -> putWord8 011 >> put t
       PrimAnd           -> putWord8 012
       PrimOr            -> putWord8 013
       PrimNot           -> putWord8 014
       PrimAddP t        -> putWord8 015 >> put t
       PrimLoad m k t    -> putWord8 016 >> put m >> put k >> put t
       PrimStore m k t   -> putWord8 017 >> put m >> put k >> put t
       PrimAAddZ x y     -> putWord8 018 >> put x >> put y
       PrimCastToOwned   -> putWord8 019
       PrimCastFromOwned -> putWord8 020
       PrimCastFromCursor -> putWord8 021
       PrimGetFrameP     -> putWord8 022
       PrimCastZToF x y  -> putWord8 023 >> put x >> put y
       PrimCastFToZ x y  -> putWord8 024 >> put x >> put y
       PrimCmpF x y      -> putWord8 025 >> put x >> put y
       PrimAddF x        -> putWord8 026 >> put x
       PrimSubF x        -> putWord8 027 >> put x
       PrimMulF x        -> putWord8 028 >> put x
       PrimModF x        -> putWord8 029 >> put x
       PrimDivF x        -> putWord8 030 >> put x
       PrimRoundF r x y z -> putWord8 031 >> put r >> put x >> put y >> put z
       PrimPowF x        -> putWord8 032 >> put x
       PrimUnaryF x y    -> putWord8 033 >> put x >> put y

  get = getWord8 >>= pick
    where
      pick 000 = PrimCastZ <$> get <*> get <*> get
      pick 001 = PrimExtendZ <$> get <*> get <*> get
      pick 002 = PrimAddZ <$> get <*> get
      pick 003 = PrimSubZ <$> get <*> get
      pick 004 = PrimMulZ <$> get <*> get
      pick 005 = PrimModZ <$> get <*> get
      pick 006 = PrimDivZ <$> get <*> get
      pick 007 = PrimMaxZ <$> get <*> get
      pick 008 = PrimMinZ <$> get <*> get
      pick 009 = PrimCmpZ <$> get <*> get <*> get
      pick 010 = PrimCmpP <$> get
      pick 011 = PrimSelect <$> get
      pick 012 = pure PrimAnd
      pick 013 = pure PrimOr
      pick 014 = pure PrimNot
      pick 015 = PrimAddP <$> get
      pick 016 = PrimLoad <$> get <*> get <*> get
      pick 017 = PrimStore <$> get <*> get <*> get
      pick 018 = PrimAAddZ <$> get <*> get
      pick 019 = pure PrimCastToOwned
      pick 020 = pure PrimCastFromOwned
      pick 021 = pure PrimCastFromCursor
      pick 022 = pure PrimGetFrameP
      pick 023 = PrimCastZToF <$> get <*> get
      pick 024 = PrimCastFToZ <$> get <*> get
      pick 025 = PrimCmpF <$> get <*> get
      pick 026 = PrimAddF <$> get
      pick 027 = PrimSubF <$> get
      pick 028 = PrimMulF <$> get
      pick 029 = PrimModF <$> get
      pick 030 = PrimDivF <$> get
      pick 031 = PrimRoundF <$> get <*> get <*> get <*> get
      pick 032 = PrimPowF <$> get
      pick 033 = PrimUnaryF <$> get <*> get
      pick _ = readError "Prim.get"

instance Binary Lit where
  put UnitL = putWord8 0
  put NullL = putWord8 1
  put NullRefL = putWord8 2
  put (BoolL True) = putWord8 3
  put (BoolL False) = putWord8 4
  put (IntL x y n) = putWord8 5 >> put x >> put y >> put n
  put (FloatL x n) = putWord8 6 >> put x >> put n
  get = getWord8 >>= pick
    where
      pick 0 = pure UnitL
      pick 1 = pure NullL
      pick 2 = pure NullRefL
      pick 3 = pure (BoolL True)
      pick 4 = pure (BoolL False)
      pick 5 = intL <$> get <*> get <*> get
      pick 6 = FloatL <$> get <*> get
      pick _ = readError "Lit.get"

instance Binary ModuleName where
  put (ModuleName mn) = put mn
  get = ModuleName <$> get

instance Binary LabelTag where
  put = putEnum
  get = getEnum "LabelTag.get"

instance Binary LocalID where
  put (LocalID n) = put n
  get = fmap LocalID get

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
  get = getWord8 >>= pick
    where
      pick 0 = VarV <$> get
      pick 1 = RecV <$> get <*> get
      pick 2 = LitV <$> get

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
    put $ funInlineRequest f
    put $ funFrameSize f
    put $ funEntryPoints f
    put $ funParams f
    put $ funReturnTypes f
    put $ funBody f
  get = do
    cc <- get
    size <- get
    uses <- get
    inl <- get
    frame_size <- get
    entry_points <- get
    params <- get
    return_types <- get
    body <- get
    return $ Fun { funConvention = cc
                 , funSize = size
                 , funUses = uses
                 , funInlineRequest = inl
                 , funFrameSize = frame_size 
                 , funEntryPoints = entry_points
                 , funParams = params
                 , funReturnTypes = return_types
                 , funBody = body}

instance Binary StaticData where
  put (StaticData v) = put v
  get = StaticData <$> get

instance (Binary a) => Binary (Def a) where
  put (Def v x) = put v >> put x
  get = Def <$> get <*> get

-- | A nonrecursive group is encoded as (0 ++ value);
--   a recursive group is encoded as ((1 + length) ++ concat values)
instance (Binary a) => Binary (Group a) where
  put (NonRec x) = put (0 :: Int) >> put x
  put (Rec xs) = put (1 + length xs :: Int) >> mapM_ put xs
  get = get >>= get_group
    where
      get_group (0 :: Int) = NonRec <$> get
      get_group (n :: Int) = Rec <$> replicateM (n - 1) get

instance Binary GlobalDef where
  put (GlobalFunDef d) = putWord8 0 >> put d
  put (GlobalDataDef d) = putWord8 1 >> put d
  get = do tag <- getWord8
           case tag of
             0 -> GlobalFunDef <$> get
             1 -> GlobalDataDef <$> get

instance Binary FunctionType where
  put ft = put (ftConvention ft) >>
           put (ftParamTypes ft) >>
           put (ftReturnTypes ft)
  get = mkFunctionType <$> get <*> get <*> get

instance Binary EntryPoints where
  put ep = put (entryPointsType ep) >>
           -- Don't need to put arity
           put (directEntry ep) >>
           put (vectorEntry ep) >>
           put (exactEntry ep) >>
           put (inexactEntry ep) >>
           put (infoTableEntry ep) >>
           put (globalClosure ep)

  get = do ftype <- get
           let arity = length $ ftParamTypes ftype
           dir <- get
           vec <- get
           exa <- get
           ine <- get
           inf <- get
           glo <- get
           return $ EntryPoints ftype arity dir vec exa ine inf glo

instance Binary Import where
  put (ImportClosureFun ep f) =
    putWord8 0 >> put ep >> put f
  put (ImportPrimFun v t f) =
    putWord8 1 >> put v >> put t >> put f
  put (ImportData v val) =
    putWord8 2 >> put v >> put val
  
  get = getWord8 >>= pick
    where
      pick 0 = ImportClosureFun <$> get <*> get
      pick 1 = ImportPrimFun <$> get <*> get <*> get
      pick 2 = ImportData <$> get <*> get
      pick _ = readError "Import.get"
