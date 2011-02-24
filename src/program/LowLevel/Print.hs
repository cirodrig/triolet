
{-# LANGUAGE PatternGuards #-}
{-# OPTIONS -fwarn-incomplete-patterns #-}
module LowLevel.Print where

import Text.PrettyPrint.HughesPJ

import Common.Identifier
import Common.Label
import Export
import LowLevel.CodeTypes
import LowLevel.Syntax

fillBracketList :: [Doc] -> Doc
fillBracketList xs = brackets $ fsep $ punctuate (text ",") xs

sepBracketList :: [Doc] -> Doc
sepBracketList xs = brackets $ sep $ punctuate (text ",") xs

pprVarLong :: Var -> Doc
pprVarLong v =
  let name_doc = text $ maybe "_" labelLocalNameAsString $ varName v
      id_doc = text $ show $ fromIdent $ varID v
  in pprValueType (varType v) <+> name_doc <> text "'" <> id_doc

pprVar :: Var -> Doc
pprVar v =
  let name_doc = text $ maybe "_" labelLocalNameAsString $ varName v
      id_doc = text $ show $ fromIdent $ varID v
  in name_doc <> text "'" <> id_doc

pprValueType :: ValueType -> Doc
pprValueType (PrimType pt) = pprPrimType pt
pprValueType (RecordType rt) = pprStaticRecord rt

pprPrimType pt = 
  case pt
  of UnitType -> text "unit"
     BoolType -> text "bool"
     IntType sign size ->
       let sgn = case sign
                 of Signed   -> 'i'
                    Unsigned -> 'u'
       in text (sgn : show_size size)
     FloatType size ->
       text ('f' : show_size size)
     PointerType -> text "ptr"
     OwnedType -> text "own"
  where
    show_size S8 = "8"
    show_size S16 = "16"
    show_size S32 = "32"
    show_size S64 = "64"

pprStaticRecord rt = pprRecordType (text . show) rt
pprDynamicRecord rt = pprRecordType pprVal rt

pprRecordType ppr_value rt =
  let fields =
        brackets $ fsep $ punctuate (text ",") $
        map (pprField ppr_value) (recordFields rt)
      sz = ppr_value $ recordSize rt
      al = ppr_value $ recordAlignment rt
  in hang (text "record" <+> sz <+> text "%" <+> al) 4 fields

pprField ppr_value fld =
  ppr_value (fieldOffset fld) <> text ":" <+> pprFieldType ppr_value (fieldType fld)

pprStaticFieldType :: StaticFieldType -> Doc
pprStaticFieldType = pprFieldType (text . show)

pprDynamicFieldType :: DynamicFieldType -> Doc
pprDynamicFieldType = pprFieldType pprVal

pprFieldType ppr_val fld = 
  case fld
  of PrimField pt -> pprPrimType pt 
     RecordField rt -> pprRecordType ppr_val rt
     BytesField sz al ->
       text "bytes" <+> ppr_val sz <+> text "%" <+> ppr_val al

pprFunctionType :: FunctionType -> Doc
pprFunctionType ftype =
  pprFunSignature
  (map pprValueType $ ftParamTypes ftype)
  (map pprValueType $ ftReturnTypes ftype)

pprStaticData (StaticData rec values) =
  parens (pprStaticRecord rec) <+> (fillBracketList $ map pprVal values)

pprDataDef :: DataDef -> Doc
pprDataDef (Def v (StaticData rec values)) =
  let initializer = fillBracketList 
                    [ mutability m <+> pprVal v
                    | (m, v) <- zip (map fieldMutable $ recordFields rec) values]
  in hang (text "data" <+> pprVar v <+> text "=") 4 initializer
  where
    mutability Constant = text "const"
    mutability Mutable  = empty

pprFunSignature :: [Doc] -> [Doc] -> Doc
pprFunSignature domain range =
  hang (sepBracketList domain) (-3) (text "->" <+> sepBracketList range)

pprFunDef :: FunDef -> Doc
pprFunDef (Def v f) =
  let intro = if isPrimFun f then text "procedure" else text "function"
      inl = if funInlineRequest f then text "INLINE" else empty
      param_doc = map pprVarLong $ funParams f
      ret_doc = map pprValueType $ funReturnTypes f
      leader = pprVar v <> pprFunSignature param_doc ret_doc
      local_doc = if funFrameSize f == 0
                  then empty
                  else text "frame size:" <+> text (show $ funFrameSize f)
  in intro <+> inl <+> leader <+> text "=" $$
     nest 4 local_doc $$
     nest 4 (pprBlock (funBody f))

pprFun :: Fun -> Doc
pprFun fun =
  let param_doc = brackets $ sep $ punctuate (text ",") $ map pprVarLong $
                  funParams fun
      ret_doc = fillBracketList $ map pprValueType $ funReturnTypes fun
      inl_doc = if funInlineRequest fun
                then text "INLINE"
                else empty
      local_doc = if funFrameSize fun == 0
                  then empty
                  else text "frame size:" <+> text (show $ funFrameSize fun)
      fun_call = inl_doc <+> case funConvention fun
                             of PrimCall -> text "lambda_p"
                                ClosureCall -> text "lambda_c"
  in fun_call <+> (hang param_doc (-3) (text "->" <+> ret_doc)) $$
     nest 4 local_doc $$
     nest 4 (pprBlock $ funBody fun)

pprInfixPrim :: Prim -> Maybe Doc
pprInfixPrim prim =
  case prim
  of PrimAddZ _ _ -> Just $ text "+"
     PrimSubZ _ _ -> Just $ text "-"
     PrimMulZ _ _ -> Just $ text "*"
     PrimModZ _ _ -> Just $ text "%"
     PrimDivZ _ _ -> Just $ text "/"
     PrimCmpZ _ _ c -> Just $ comparison c
     PrimCmpP c -> Just $ comparison c
     PrimAnd -> Just $ text "&&"
     PrimOr -> Just $ text "||"
     PrimAddP -> Just $ text "^+"
     PrimCmpF _ c -> Just $ comparison c
     PrimAddF _ -> Just $ text "+"
     PrimSubF _ -> Just $ text "-"
     PrimMulF _ -> Just $ text "*"
     PrimModF _ -> Just $ text "%"
     PrimDivF _ -> Just $ text "/"
     PrimPowF _ -> Just $ text "**"
     _ -> Nothing
  where
    comparison c =
      case c
      of CmpEQ -> text "=="
         CmpNE -> text "/="
         CmpLT -> text "<"
         CmpLE -> text "<="
         CmpGT -> text ">"
         CmpGE -> text ">="

pprPrim prim =
  let name =
        case prim
        of PrimCastZ in_sgn out_sgn sz ->
             "cast_" ++ sign in_sgn ++ "_" ++ sign out_sgn
           PrimExtendZ Signed in_sz out_sz
             | in_sz < out_sz -> "sxt_" ++ size in_sz ++ "_" ++ size out_sz
           PrimExtendZ Unsigned in_sz out_sz
             | in_sz < out_sz -> "zxt_" ++ size in_sz ++ "_" ++ size out_sz
           PrimExtendZ _ in_sz out_sz ->
             "trunc_" ++ size in_sz ++ "_" ++ size out_sz
           PrimAddZ _ _ -> "add"
           PrimSubZ _ _ -> "sub"
           PrimMulZ _ _ -> "mul"
           PrimModZ _ _ -> "mod"
           PrimDivZ _ _ -> "div"
           PrimMaxZ _ _ -> "max"
           PrimMinZ _ _ -> "min"
           PrimCmpZ _ _ c -> comparison c
           PrimCmpP c -> comparison c
           PrimAnd -> "and"
           PrimOr -> "or"
           PrimNot -> "not"
           PrimAddP   -> "ptradd"
           PrimLoad Mutable _ -> "load"
           PrimLoad Constant _ -> "load const"
           PrimStore Mutable _ -> "store"
           PrimStore Constant _ -> "store const"
           PrimAAddZ _ _ -> "atomic_add"
           PrimCastToOwned -> "cast_ptr_own"
           PrimCastFromOwned -> "cast_own_ptr"
           PrimGetFrameP -> "get_frame_ptr"
           PrimCastFToZ _ _ -> "cast_float_int"
           PrimCastZToF _ _ -> "cast_int_float"
           PrimCmpF _ c -> comparison c
           PrimAddF _ -> "fadd"
           PrimSubF _ -> "fsub"
           PrimMulF _ -> "fmul"
           PrimModF _ -> "fmod"
           PrimDivF _ -> "fdiv"
           PrimRoundF Floor _ _ _ -> "floor"
           PrimRoundF Ceiling _ _ _ -> "ceil"
           PrimRoundF Nearest _ _ _ -> "round"
           PrimRoundF Truncate _ _ _ -> "trunc"
           PrimPowF _ -> "fpow"
           PrimUnaryF op _ -> unary_float op
      ty =
        case prim
        of PrimLoad _ t -> pprValueType t
           PrimStore _ t -> pprValueType t
           _ -> empty
  in text name <+> ty
  where
    unary_float op =
      case op
      of ExpI -> "fexp"
         LogI -> "flog"
         SqrtI -> "fsqrt"
         SinI -> "fsin"
         CosI -> "fcos"
         TanI -> "ftan"
    comparison c =
      case c
      of CmpEQ -> "cmp_eq"
         CmpNE -> "cmp_ne"
         CmpLT -> "cmp_lt"
         CmpLE -> "cmp_le"
         CmpGT -> "cmp_gt"
         CmpGE -> "cmp_ge"      
    sign Signed = "i"
    sign Unsigned = "u"
    size S8 = "8"
    size S16 = "16"
    size S32 = "32"
    size S64 = "64"

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
     LitV l -> pprLit l
     LamV f -> parens $ pprFun f

pprAtom atom =
  case atom
  of ValA vs -> arg_list vs
     CallA conv v vs -> 
       let conv_doc = case conv
                      of ClosureCall -> text "call" 
                         PrimCall -> text "primcall"
       in conv_doc <+> pprVal v <> arg_list vs
     PrimA p [v1, v2] 
       | Just infix_op <- pprInfixPrim p ->
           pprVal v1 <+> infix_op <+> pprVal v2
     PrimA p vs -> pprPrim p <> arg_list vs
     PackA rt vs -> hang (text "pack" <> arg_list vs) 8 $
                    text "as" <+> pprStaticRecord rt
     UnpackA rt v -> text "unpack" <+> pprVal v <+> text "as" <+> pprStaticRecord rt
  where
    arg_list vs = fillBracketList $ map pprVal vs

pprStm :: Stm -> Doc
pprStm stmt = 
  case stmt
  of LetE [] atom body -> text "[] <-" <+> pprAtom atom $$ pprStm body
     LetE vars atom body ->
       let binder = sep $ punctuate (text ",") $ map pprVarLong vars
           rhs = pprAtom atom
       in hang (binder <+> text "<-") 8 rhs $$ pprStm body
     LetrecE defs body ->
       text "let" <+> pprGroup pprFunDef defs $$
       pprStm body
     SwitchE val alts -> text "switch" <> parens (pprVal val) $$
                         nest 2 (vcat $ map print_alt alts)
     ReturnE atom -> pprAtom atom
  where
    print_alt (lit, body) = hang (pprLit lit <> text ":") 6 (pprBlock body)

pprBlock stmt = pprStm stmt

pprImport :: Import -> Doc
pprImport impent = text "extern" <+>
  case impent
  of ImportClosureFun entry_points mfun ->
       let ftype = entryPointsType entry_points
           signature =
             pprFunSignature
             (map pprValueType $ ftParamTypes ftype)
             (map pprValueType $ ftReturnTypes ftype)
           impvar = case globalClosure entry_points
                    of Just v  -> pprVar v
                       Nothing -> text "<ERROR>"
           value = case mfun
                   of Nothing -> empty
                      Just f  -> pprFun f
       in hang (text "function" <+> impvar <+> signature) 4 value
     ImportPrimFun v ftype mfun ->
       let signature =
             pprFunSignature
             (map pprValueType $ ftParamTypes ftype)
             (map pprValueType $ ftReturnTypes ftype)
           value = case mfun
                   of Nothing -> empty
                      Just f  -> pprFun f
       in hang (text "procedure" <+> pprVar v <+> signature) 4 value
     ImportData v value ->
       let value_doc =
             case value
             of Nothing -> empty
                Just sd -> text "=" <+> pprStaticData sd
       in text "data" <+> pprVar v <+> value_doc

pprDataDefs :: [DataDef] -> Doc
pprDataDefs defs = vcat $ map pprDataDef defs

pprFunDefs :: [FunDef] -> Doc
pprFunDefs defs = vcat $ map pprFunDef defs

pprImports :: [Import] -> Doc
pprImports imports = vcat $ map pprImport imports

pprExports :: [(Var, ExportSig)] -> Doc
pprExports exports = vcat [text "export" <+> pprVar v | (v, _) <- exports]

pprGlobalDef (GlobalDataDef d) = pprDataDef d
pprGlobalDef (GlobalFunDef d) = pprFunDef d

pprGlobalDefs defs = vcat $ map (pprGroup pprGlobalDef) defs

pprGroup pr (NonRec x) = text "nonrec {" $$ nest 2 (pr x) $$ text "}"
pprGroup pr (Rec xs) = text "rec {" $$ nest 2 (vcat $ map pr xs) $$ text "}"

pprModule :: Module -> Doc
pprModule (Module modname _ imports defs exports) =
  text "module" <+> text (showModuleName modname) $$
  pprImports imports $$
  pprGlobalDefs defs $$
  pprExports exports