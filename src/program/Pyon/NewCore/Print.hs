
module Pyon.NewCore.Print
       (pprVar, pprVal, pprStm, pprDef, pprModule)
where

import Data.Maybe
import Text.PrettyPrint.HughesPJ
import Gluon.Common.Label
import qualified Gluon.Core as Gluon
import Pyon.NewCore.Syntax

data PrintFlags = PrintFlags

-- UTF-8 for lowercase lambda
lambda = text [toEnum 0xCE, toEnum 0xBB]

-- Print stacked with braces and semicolons
bracesStack :: [Doc] -> Doc
bracesStack [] = braces empty
bracesStack (x:xs) =
  let first = text "{" <+> x
      rest = map (semi <+>) xs
      last = text "}"
  in vcat (first : rest ++ [last])

defaultPrintFlags :: PrintFlags
defaultPrintFlags = PrintFlags

pprVar :: Var -> Doc
pprVar = pprVarFlags defaultPrintFlags

pprVal :: CVal -> Doc
pprVal = pprValFlags defaultPrintFlags

pprStm :: CStm -> Doc
pprStm = pprStmFlags defaultPrintFlags

pprDef :: CDef -> Doc
pprDef = pprDefFlags defaultPrintFlags

pprModule :: Module Core -> Doc
pprModule (Module m) = vcat $ map (<> semi) $ map pprDef m 

pprVarFlags :: PrintFlags -> Var -> Doc
pprVarFlags _ v = Gluon.pprVar v

pprValFlags :: PrintFlags -> CVal -> Doc
pprValFlags flags val =
  case val
  of GluonV {valGluonTerm = t} -> Gluon.pprExp t
     AppV {valOper = op, valArgs = args} ->
       sep $ map (parens . pprValFlags flags) (op : args)
     ALamV {valAFun = fun} ->
       pprActionFunFlags flags Nothing fun
     SLamV {valSFun = fun} ->
       pprStreamFunFlags flags Nothing fun
     SDoV {valStm = stm} ->
       text "do" <+> pprStmFlags flags stm

pprBinderFlags :: PrintFlags -> Binder Core () -> Doc
pprBinderFlags flags (Binder v ty ()) =
  pprVarFlags flags v <+> colon <+> Gluon.pprExp ty

pprStmFlags :: PrintFlags -> CStm -> Doc
pprStmFlags flags stm =
  case stm
  of ReturnS {stmVal = val} ->
       text "return" <+> pprValFlags flags val
     CallS {stmVal = val} ->
       pprValFlags flags val
     CaseS {stmScrutinee = scr, stmAlts = alts} -> 
       text "case" <+> pprValFlags flags scr $$ 
       text "of" <+> vcat (map (pprAltFlags flags) alts)
     _ -> pprBlockFlags flags stm

-- Print a statement in "block" format
pprBlockFlags :: PrintFlags -> CStm -> Doc
pprBlockFlags flags stm = bracesStack $ pprStatements stm
  where
    pprStatements (LetS {stmVar = Nothing, stmStm = rhs, stmBody = body}) =
      pprStmFlags flags rhs : pprStatements body
    pprStatements (LetS {stmVar = Just v, stmStm = rhs, stmBody = body}) =
      let line = hang (pprVarFlags flags v <+> text "<-") 4 $ 
                 pprStmFlags flags rhs 
      in line : pprStatements body
    pprStatements (LetrecS {stmDefs = defs, stmBody = body}) =
      let line = hang (text "letrec") 2 $
                 vcat $ punctuate semi $ map (pprDefFlags flags) defs
      in line : pprStatements body
    pprStatements s = [pprStmFlags flags s]

pprAltFlags flags (Alt {altPat = pat, altBody = body}) =
  let pattern = pprPat pat
      rest = pprStmFlags flags body
  in hang (pattern <> text ".") 4 rest
  where
    pprPat (ConP con params) =
      hsep (text (showLabel $ conName con) : map pprParam params)

    pprParam RigidP        = text "_"
    pprParam (FlexibleP v) = pprVarFlags flags v

pprDefFlags flags (Def {definiendum = v, definiens = def}) =
  let definiendum_doc = pprVarFlags flags v
  in case def
     of ActionFunDef f -> pprActionFunFlags flags (Just definiendum_doc) f
        StreamFunDef f -> pprStreamFunFlags flags (Just definiendum_doc) f

pprActionFunFlags flags fun_name fun =
  pprFunFlags flags fun_name (pprStmFlags flags) fun

pprStreamFunFlags flags fun_name fun =
  pprFunFlags flags fun_name (pprValFlags flags) fun
  
pprFunFlags flags fun_name print_body fun =
  let opening = fromMaybe lambda fun_name
      params = map parens $ map (pprBinderFlags flags) $ funParams fun
      ret_type = nest (-3) $ text "->" <+> Gluon.pprExp (funReturnType fun)
      eff_type = nest (-2) $ text "|" <+> Gluon.pprExp (funEffectType fun)
      header = opening <+> sep (params ++ [ret_type, eff_type])
      header_sep = case fun_name
                   of Nothing -> header <> text "."
                      Just _  -> header <+> equals
      body = print_body $ funBody fun
  in hang header_sep 4 body
