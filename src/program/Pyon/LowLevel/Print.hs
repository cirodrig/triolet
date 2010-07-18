
module Pyon.LowLevel.Print where

import Text.PrettyPrint.HughesPJ

import Gluon.Common.Label
import Gluon.Common.Identifier
import qualified Gluon.Core as Gluon
import Pyon.LowLevel.Types
import Pyon.LowLevel.Record
import Pyon.LowLevel.Syntax

fillBracketList :: [Doc] -> Doc
fillBracketList xs = brackets $ fsep $ punctuate (text ",") xs

pprVarLong :: Var -> Doc
pprVarLong v =
  let name_doc = text $ maybe "_" showLabel $ varName v
      id_doc = text $ show $ fromIdent $ varID v
  in pprValueType (varType v) <+> name_doc <> text "'" <> id_doc

pprVar :: Var -> Doc
pprVar v =
  let name_doc = text $ maybe "_" showLabel $ varName v
      id_doc = text $ show $ fromIdent $ varID v
  in name_doc <> text "'" <> id_doc

pprValueType :: ValueType -> Doc
pprValueType (PrimType pt) = pprPrimType pt
pprValueType (RecordType rt) = pprRecordType rt

pprPrimType UnitType = text "unit"
pprPrimType BoolType = text "bool"
pprPrimType (IntType sign size) =
  let sgn = case sign
            of Signed   -> 's'
               Unsigned -> 'u'
      sz  = case size
            of S8 -> "8"
               S16 -> "16"
               S32 -> "32"
               S64 -> "64"
  in text (sgn : sz)
pprPrimType (FloatType S32) = text "float"
pprPrimType (FloatType S64) = text "double"
pprPrimType PointerType = text "ptr"
pprPrimType OwnedType = text "owned"

pprRecordType rt =
  brackets $ fsep $ punctuate (text ",") $
  map (pprFieldType . fieldType) $ recordFields rt

pprFieldType (PrimField pt) = pprPrimType pt 
pprFieldType (RecordField _ rt) = pprRecordType rt
pprFieldType (BytesField _ _) = text "BYTES"

pprDef :: FunDef -> Doc
pprDef (FunDef v f) = hang (pprVar v <+> text "=") 4 $ pprFun f

pprFun :: Fun -> Doc
pprFun (Fun params rt body) =
  let param_doc = brackets $ sep $ punctuate (text ",")  $ map pprVarLong params
      ret_doc = fillBracketList $ map pprValueType rt
  in text "lambda" <+> (hang param_doc (-3) (text "->" <+> ret_doc)) $$
     nest 4 (pprBlock body)

pprPrim prim = text "PRIM"

pprLit literal =
  case literal
  of UnitL -> text "unit"
     NullL -> text "null"
     BoolL True -> text "true"
     BoolL False -> text "false"
     IntL sgn sz n -> parens $ pprPrimType (IntType sgn sz) <+> text (show n)
     FloatL sz d -> parens $ pprPrimType (FloatType sz) <+> text (show d)

pprVal value =
  case value
  of VarV v -> pprVar v
     RecV _ vs -> fillBracketList $ map pprVal vs
     ConV c -> text $ showLabel $ Gluon.conName c 
     LitV l -> pprLit l
     LamV f -> parens $ pprFun f

pprAtom atom =
  case atom
  of ValA vs -> arg_list vs
     CallA v vs -> text "call" <+> pprVal v <> arg_list vs
     PrimCallA v vs -> text "primcall" <+> pprVal v <> arg_list vs
     PrimA p vs -> pprPrim p <> arg_list vs
     PackA rt vs -> hang (text "pack" <> arg_list vs) 8 $
                    text "as" <+> pprRecordType rt
     UnpackA rt v -> text "unpack" <+> pprVal v <+> text "as" <+> pprRecordType rt
     SwitchA val alts -> text "switch" <> parens (pprVal val) $$
                         nest 2 (vcat $ map print_alt alts)
  where
    arg_list vs = fillBracketList $ map pprVal vs
    print_alt (lit, body) = hang (pprLit lit <> text ":") 6 (pprBlock body)

pprStm :: Stm -> Doc
pprStm stmt = 
  case stmt
  of LetE [] atom -> text "[] <-" <+> pprAtom atom
     LetE vars atom ->
       let binder = sep $ punctuate (text ",") $ map pprVarLong vars
           rhs = pprAtom atom
       in hang (binder <+> text "<-") 8 rhs
     LetrecE defs ->
       text "letrec" $$
       nest 8 (pprDefs defs)

pprBlock (Block xs atom) = vcat (map pprStm xs) $$ text "return" <+> pprAtom atom

pprDefs :: [FunDef] -> Doc
pprDefs defs = vcat $ map pprDef defs

pprModule :: Module -> Doc
pprModule (Module defs _) = pprDefs defs