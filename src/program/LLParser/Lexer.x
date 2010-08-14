
{
module LLParser.Lexer(Token(..), showToken, T(..), showT, lexFile) where

import System.FilePath
import LLParser.LexCode
}

$digit = [0-9]
$alpha = [a-zA-Z_]
$ident = [a-zA-Z_0-9]
$space = [\ \n\t]
$symbol = [=\~!@\#\$\%\^&\*\-\+\?\\\|\/]

@space = $space+
@uint = $digit+
@int = \-? @uint
@float = $digit+(\.$digit+)?
@word = $alpha $ident*
@notid = [.\n] # $ident
@notsym = [.\n] # $symbol

rules :-

@space		;

-- C preprocessor line directives
^\# $space+ @uint $space+ .* $ { lineDirective }

-- Keywords
"alignof" / @notid	{ tok AlignofTok }
"as" / @notid		{ tok AsTok }
"bytes" / @notid	{ tok BytesTok }
"call" / @notid		{ tok CallTok }
"data" / @notid		{ tok DataTok }
"else" / @notid		{ tok ElseTok }
"function" / @notid	{ tok FunctionTok }
"if" / @notid		{ tok IfTok }
"int8" / @notid		{ tok Int8Tok }
"int16" / @notid	{ tok Int16Tok }
"int32" / @notid	{ tok Int32Tok }
"int64" / @notid	{ tok Int64Tok }
"null" / @notid		{ tok NullTok }
"owned" / @notid	{ tok OwnedTok }
"pointer" / @notid	{ tok PointerTok }
"primcall" / @notid	{ tok PrimCallTok }
"procedure" / @notid	{ tok ProcedureTok }
"record" / @notid	{ tok RecordTok }
"sizeof" / @notid	{ tok SizeofTok }
"uint8" / @notid	{ tok UInt8Tok }
"uint16" / @notid	{ tok UInt16Tok }
"uint32" / @notid	{ tok UInt32Tok }
"uint64" / @notid	{ tok UInt64Tok }

-- Punctuation

"{"			{ tok LBraceTok }
"}"			{ tok RBraceTok }
"("			{ tok LParenTok }
")"			{ tok RParenTok }
"->" / @notsym		{ tok ArrowTok }
"=" / @notsym		{ tok AssignTok }
";"			{ tok SemiTok }
","			{ tok CommaTok }

-- Operators
"==" / @notsym		{ tok EqualTok }
"."			{ tok DotTok }
"@!" / @notsym		{ tok FieldTok }
"@" / @notsym		{ tok AtTok }
"!+" / @notsym		{ tok DerefPlusTok }
"*"			{ tok StarTok }

-- Other symbols
@word			{ idTok }
@int			{ intTok }

{

-- | Scan an entire file and generate a stream of tokens.  Throw an error
-- if a syntax error occurs.
scan :: AlexInput -> Int -> [T]
scan inp sc =
  case alexScan inp sc
  of AlexToken inp' n a -> runAction a scan inp inp' sc n
     AlexSkip inp' _    -> scan inp' sc
     AlexEOF            -> []
     AlexError inp'     -> error $ "Syntax error at " ++ show (inputPos inp')

-- | Perform lexical analysis on a file.  Return a sequence of tokens.
-- Append a newline to ensure correct end-of-file behavior.
-- If a syntax error occurs, an exception is thrown.
lexFile :: FilePath -> String -> [T]
lexFile path contents = scan (fileInput path (contents ++ "\n")) 0

}