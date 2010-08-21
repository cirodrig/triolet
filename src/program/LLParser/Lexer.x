
{
module LLParser.Lexer(Token(..), showToken, T(..), showT, lexFile) where

import System.FilePath
import LLParser.LexCode
}

$digit = [0-9]
$alpha = [a-zA-Z_]
$ident = [a-zA-Z_0-9]
$space = [\ \n\t]
$symbol = [=\~!@\#\$\%\^&\*\-\+\?\\\|\/] -- Valid operator character
$string = [^\"\\\n]			 -- Valid character in string

@space = $space+
@uint = $digit+
@int = \-? @uint
@float = $digit+\.$digit+
@word = $alpha $ident*
@string = $string*
@notid = [.\n] # $ident
@notsym = [.\n] # $symbol

rules :-

@space			;

-- C preprocessor line directives
^\# $space+ @uint $space+ .* $ { lineDirective }

-- Keywords
"alignof" / @notid	{ tok AlignofTok }
"as" / @notid		{ tok AsTok }
"bool" / @notid		{ tok BoolTok }
"bytes" / @notid	{ tok BytesTok }
"call" / @notid		{ tok CallTok }
"data" / @notid		{ tok DataTok }
"double" / @notid	{ tok DoubleTok }
"else" / @notid		{ tok ElseTok }
"extern" / @notid	{ tok ExternTok }
"false" / @notid	{ tok FalseTok }
"float" / @notid	{ tok FloatTok }
"function" / @notid	{ tok FunctionTok }
"if" / @notid		{ tok IfTok }
"import" / @notid	{ tok ImportTok }
"int8" / @notid		{ tok Int8Tok }
"int16" / @notid	{ tok Int16Tok }
"int32" / @notid	{ tok Int32Tok }
"int64" / @notid	{ tok Int64Tok }
"load" / @notid		{ tok LoadTok }
"module" / @notid	{ tok ModuleTok }
"null" / @notid		{ tok NullTok }
"owned" / @notid	{ tok OwnedTok }
"pointer" / @notid	{ tok PointerTok }
"primcall" / @notid	{ tok PrimCallTok }
"procedure" / @notid	{ tok ProcedureTok }
"record" / @notid	{ tok RecordTok }
"sizeof" / @notid	{ tok SizeofTok }
"true" / @notid		{ tok TrueTok }
"uint8" / @notid	{ tok UInt8Tok }
"uint16" / @notid	{ tok UInt16Tok }
"uint32" / @notid	{ tok UInt32Tok }
"uint64" / @notid	{ tok UInt64Tok }
"_" / @notid @		{ tok WildTok }

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
"!=" / @notsym		{ tok NotEqualTok }
"."			{ tok DotTok }
"@!" / @notsym		{ tok FieldTok }
"@" / @notsym		{ tok AtTok }
"!" / @notsym		{ tok DerefTok }
"+" / @notsym		{ tok PlusTok }
"-" / @notsym		{ tok MinusTok }
"^+" / @notsym		{ tok PointerPlusTok }
"%" / @notsym		{ tok PercentTok }
"*"			{ tok StarTok }
"!+" / @notsym		{ tok DerefPlusTok }

-- Other symbols
\" @string \"		{ stringTok }
@word			{ idTok }
@float			{ floatTok }
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