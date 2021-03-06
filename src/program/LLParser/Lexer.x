
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
@wordtag = @word (\' $alpha )*
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
"base" / @notid		{ tok BaseTok }
"bool" / @notid		{ tok BoolTok }
"call" / @notid		{ tok CallTok }
"const" / @notid	{ tok ConstTok }
"cursor" / @notid	{ tok CursorTok }
"data" / @notid		{ tok DataTok }
"double" / @notid	{ tok DoubleTok }
"else" / @notid		{ tok ElseTok }
"extern" / @notid	{ tok ExternTok }
"false" / @notid	{ tok FalseTok }
"float" / @notid	{ tok FloatTok }
"function" / @notid	{ tok FunctionTok }
"if" / @notid		{ tok IfTok }
"import" / @notid	{ tok ImportTok }
"inline" / @notid	{ tok InlineTok }
"int8" / @notid		{ tok Int8Tok }
"int16" / @notid	{ tok Int16Tok }
"int32" / @notid	{ tok Int32Tok }
"int64" / @notid	{ tok Int64Tok }
"letrec" / @notid	{ tok LetrecTok }
"load" / @notid		{ tok LoadTok }
"module" / @notid	{ tok ModuleTok }
"memory_barrier" / @notid { tok MemoryBarrierTok }
"nil" / @notid		{ tok NilTok }
"null" / @notid		{ tok NullTok }
"owned" / @notid	{ tok OwnedTok }
"pointer" / @notid	{ tok PointerTok }
"primcall" / @notid	{ tok PrimCallTok }
"procedure" / @notid	{ tok ProcedureTok }
"record" / @notid	{ tok RecordTok }
"sizeof" / @notid	{ tok SizeofTok }
"true" / @notid		{ tok TrueTok }
"typedef" / @notid	{ tok TypedefTok }
"uint8" / @notid	{ tok UInt8Tok }
"uint16" / @notid	{ tok UInt16Tok }
"uint32" / @notid	{ tok UInt32Tok }
"uint64" / @notid	{ tok UInt64Tok }
"unit" / @notid		{ tok UnitTok }
"value" / @notid	{ tok ValueTok }
"while" / @notid	{ tok WhileTok }
"_" / @notid		{ tok WildTok }

-- Punctuation
"{"			{ tok LBraceTok }
"}"			{ tok RBraceTok }
"["			{ tok LBracketTok }
"]"			{ tok RBracketTok }
"("			{ tok LParenTok }
")"			{ tok RParenTok }
"->" / @notsym		{ tok ArrowTok }
"=" / @notsym		{ tok AssignTok }
";"			{ tok SemiTok }
","			{ tok CommaTok }

-- Operators
"==" / @notsym		{ tok EqualTok }
"!=" / @notsym		{ tok NotEqualTok }
"<" / @notsym		{ tok LessThanTok }
"<=" / @notsym		{ tok LessEqualTok }
">" / @notsym		{ tok GreaterThanTok }
">=" / @notsym		{ tok GreaterEqualTok }
"."			{ tok DotTok }
"@!" / @notsym		{ tok FieldTok }
"@" / @notsym		{ tok AtTok }
"!" / @notsym		{ tok DerefTok }
"+" / @notsym		{ tok PlusTok }
"-" / @notsym		{ tok MinusTok }
"^+" / @notsym		{ tok PointerPlusTok }
"^-" / @notsym		{ tok PointerMinusTok }
"%" / @notsym		{ tok PercentTok }
"%/" / @notsym		{ tok IntegerDivideTok }
"/" / @notsym		{ tok DivideTok }
"*"			{ tok StarTok }
"!+" / @notsym		{ tok DerefPlusTok }
"&&" / @notsym		{ tok AndTok }
"||" / @notsym		{ tok OrTok }
"~#" / @notsym		{ tok ComplementTok }
"~" / @notsym		{ tok NotTok }

-- Other symbols
\" @string \"		{ stringTok }
@wordtag		{ idTok }
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