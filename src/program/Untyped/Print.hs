
module Untyped.Print
       (pprVariable, pprPattern, pprExpression, pprModule)
where

import Text.PrettyPrint.HughesPJ
import Gluon.Common.Identifier
import Gluon.Common.Label
import Untyped.Syntax

showTuple :: [Doc] -> Doc
showTuple = parens . sep . punctuate comma

showBlock :: [Doc] -> Doc
showBlock []     = text "{}"
showBlock [d]    = d
showBlock (d:ds) = vcat ((text "{" <+> d) : (map (semi <+>) ds ++ [text "}"]))

pprLit :: Lit -> Doc
pprLit (IntL n) = text $ show n
pprLit (FloatL d) = text $ show d
pprLit (BoolL b) = text $ show b
pprLit NoneL = text "None"

pprVariable :: Variable -> Doc
pprVariable v =
  let name = maybe "_" showLabel $ varName v 
      num  = show $ fromIdent $ varID v
  in text $ name ++ "'" ++ num

pprPattern :: Pattern -> Doc
pprPattern pat =
  case pat
  of WildP {} ->
       text "_"
     VariableP {patVariable = v} ->
       pprVariable v
     TupleP {patFields = fs} ->
       showTuple $ map pprPattern fs

pprExpression :: Expression -> Doc
pprExpression exp =
  case exp
  of VariableE {expVar = v} -> pprVariable v
     LiteralE {expLit = l} -> pprLit l
     UndefinedE {} -> text "__undefined__"
     TupleE {expFields = fs} -> showTuple $ map pprExpression fs
     CallE {expOperator = op, expOperands = args} ->
       pprExpression op <> showTuple (map pprExpression args)
     IfE {expCondition = c, expIfTrue = t, expIfFalse = f} ->
       text "if" <+> pprExpression c $$
       text "then" <+> pprBlock t $$
       text "else" <+> pprBlock f
     FunE {expFunction = f} -> pprFunction Nothing f
     LetE {} -> pprBlock exp
     LetrecE {} -> pprBlock exp

pprBlock :: Expression -> Doc
pprBlock e = showBlock $ pprAsStatements e
  where
    pprAsStatements expr =
      case expr
      of LetE {expPattern = WildP {}, expArgument = rhs, expBody = body} ->
           pprExpression rhs : pprAsStatements body
         LetE {expPattern = pat, expArgument = rhs, expBody = body} ->
           let lhs_doc = pprPattern pat <+> text "="
               rhs_doc = pprExpression rhs
           in text "let" <+> hang lhs_doc 4 rhs_doc : pprAsStatements body
         LetrecE {expDefinitions = defs, expBody = body} ->
           let defs_doc = showBlock $ map pprDefinition defs
           in (text "letrec" $$ nest 2 defs_doc) : pprAsStatements body
         _ -> [pprExpression expr]

pprDefinition :: FunctionDef -> Doc
pprDefinition (FunctionDef name fun) = 
  pprFunction (Just $ pprVariable name) fun

pprFunction :: Maybe Doc -> Function -> Doc
pprFunction fname (Function { funQVars = qvars 
                            , funParameters = params
                            , funReturnType = rt
                            , funBody = body
                            }) = do
  let forall_doc = case qvars
                   of Nothing -> empty
                      Just vs -> text "forall" <+> text "..."
      intro = case fname
              of Nothing -> text "lambda" <+> param_doc <> text "."
                 Just v  -> v <+> param_doc <+> text "="
      rt_doc = case rt
               of Nothing -> empty
                  Just d  -> nest (-3) $ text "->" <+> text "..."
      param_doc = sep (map (parens . pprPattern) params ++ [rt_doc])
    in forall_doc $$ intro $$ nest 2 (pprExpression body)

pprExport :: Export -> Doc
pprExport (Export _ spec v ty) =
  text "export" <+> pprVariable v <+> text ":" <+> text "..."
  
pprModule :: Module -> Doc
pprModule (Module module_name defss exps) =
  text "module" <+> text (showModuleName module_name) $$
  vcat (map (showBlock . map pprDefinition) defss) $$
  vcat (map pprExport exps)