
{-# LANGUAGE ViewPatterns #-}
module LLParser.LexCode
       (Token(..),
        showToken,
        T(..),
        showT,
        Action(runAction),
        Input(..),
        fileInput,
        AlexInput,
        alexGetChar,
        alexGetByte,
        alexInputPrevChar,
        idTok, intTok, floatTok, stringTok, tok,
        lineDirective
       )
where

import Data.Char
import Data.List
import Data.Word
import Common.SourcePos

-- | A token produced by lexical analysis
data Token =
    -- | An identifier with label tags
    IdTok !String [String]
  | IntTok !Integer
  | FltTok !Double
  | StringTok !String
  | LBraceTok
  | RBraceTok
  | LBracketTok
  | RBracketTok
  | LParenTok
  | RParenTok
  | AssignTok
  | ArrowTok
  | SemiTok
  | CommaTok
  | EqualTok
  | NotEqualTok
  | LessThanTok
  | LessEqualTok
  | GreaterThanTok
  | GreaterEqualTok
  | DotTok
  | FieldTok
  | AtTok
  | DerefTok
  | PlusTok
  | MinusTok
  | PointerMinusTok
  | PointerPlusTok
  | PercentTok
  | IntegerDivideTok
  | DivideTok
  | StarTok
  | DerefPlusTok
  | AndTok
  | OrTok
  | NotTok
  | ComplementTok
  | WildTok
  | AlignofTok
  | AsTok
  | BaseTok
  | BoolTok
  | CallTok
  | ConstTok
  | CursorTok
  | DataTok
  | DoubleTok
  | ElseTok
  | ExternTok
  | FalseTok
  | FloatTok
  | FunctionTok
  | IfTok
  | ImportTok
  | InlineTok
  | Int8Tok
  | Int16Tok
  | Int32Tok
  | Int64Tok
  | LetrecTok
  | LoadTok
  | ModuleTok
  | MemoryBarrierTok
  | NilTok
  | NullTok
  | OwnedTok
  | PointerTok
  | PrimCallTok
  | ProcedureTok
  | RecordTok
  | SizeofTok
  | TrueTok
  | TypedefTok
  | UInt8Tok
  | UInt16Tok
  | UInt32Tok
  | UInt64Tok
  | UnitTok
  | ValueTok
  | WhileTok
    deriving(Eq)

showToken :: Token -> String
showToken (IdTok s tags) = show $ intercalate "\'" (s : tags)
showToken (IntTok n) = show n
showToken (FltTok d) = show d
showToken (StringTok s) = show s
showToken LBraceTok = "left brace"
showToken RBraceTok = "right brace"
showToken LBracketTok = "left bracket"
showToken RBracketTok = "right bracket"
showToken LParenTok = "left parenthesis"
showToken RParenTok = "right parenthesis"
showToken AssignTok = "equal sign"
showToken ArrowTok = "arrow"
showToken SemiTok = "semicolon"
showToken CommaTok = "comma"
showToken EqualTok = "equality operator"
showToken NotEqualTok = "disequality operator"
showToken LessThanTok = "less-than operator"
showToken LessEqualTok = "'<=' operator"
showToken GreaterThanTok = "greater-than operator"
showToken GreaterEqualTok = "'>=' operator"
showToken DotTok = "dot"
showToken FieldTok = "field operator"
showToken AtTok = "at operator"
showToken DerefTok = "exclamation mark"
showToken PlusTok = "plus"
showToken MinusTok = "minus"
showToken PointerMinusTok = "'^-'"
showToken PointerPlusTok = "'^+'"
showToken PercentTok = "percent sign"
showToken IntegerDivideTok = "integer division sign"
showToken DivideTok = "forward slash"
showToken StarTok = "asterisk"
showToken DerefPlusTok = "'!+'"
showToken AndTok = "boolean and"
showToken OrTok = "boolean or"
showToken NotTok = "boolean not"
showToken ComplementTok = "bitwise complement"
showToken WildTok = "wildcard"
showToken AlignofTok = "'alignof'"
showToken AsTok = "'as'"
showToken BaseTok = "'base'"
showToken BoolTok = "'bool'"
showToken CallTok = "'call'"
showToken ConstTok = "'const'"
showToken CursorTok = "'cursor'"
showToken DataTok = "'data'"
showToken DoubleTok = "'double'"
showToken ElseTok = "'else'"
showToken ExternTok = "'extern'"
showToken FalseTok = "'false'"
showToken FloatTok = "'float'"
showToken FunctionTok = "'function'"
showToken IfTok = "'if'"
showToken ImportTok = "'import'"
showToken InlineTok = "'inline'"
showToken Int8Tok = "'int8'"
showToken Int16Tok = "'int16'"
showToken Int32Tok = "'int32'"
showToken Int64Tok = "'int64'"
showToken LetrecTok = "'letrec'"
showToken LoadTok = "'load'"
showToken ModuleTok = "'module'"
showToken MemoryBarrierTok = "'memory_barrier'"
showToken NilTok = "'nil'"
showToken NullTok = "'null'"
showToken OwnedTok = "'owned'"
showToken PointerTok = "'pointer'"
showToken PrimCallTok = "'primcall'"
showToken ProcedureTok = "'procedure'"
showToken RecordTok = "'record'"
showToken SizeofTok = "'sizeof'"
showToken TrueTok = "'true'"
showToken TypedefTok = "'typedef'"
showToken UInt8Tok = "'uint8'"
showToken UInt16Tok = "'uint16'"
showToken UInt32Tok = "'uint32'"
showToken UInt64Tok = "'uint64'"
showToken UnitTok = "'unit'"
showToken ValueTok = "'value'"
showToken WhileTok = "'while'"

-- | A token labeled with a source position
data T = T !SourcePos !Token

showT (T _ tok) = showToken tok

-- | The lexer's input state
data Input =
  Input
  { inputString :: String
  , inputPrevChar :: !Char
  , inputPos :: !SourcePos
  }

-- | Use contents of a file as the lexer's input
fileInput :: FilePath -> String -> Input
fileInput path contents =
  Input { inputString = contents
        , inputPrevChar = '\n'
        , inputPos = fileSourcePos path 1 1
        }

-- | Given a character and the source position where the character begins,
-- determine the position where the next character begins.
advancePosition '\n' pos =
  case sourceLine pos
  of Just l -> setSourceColumn 1 $ setSourceLine (l+1) pos

advancePosition c pos =
  case sourceColumn pos
  of Just c -> setSourceColumn (c+1) pos

-- * Types and functions expected by Alex

type AlexInput = Input

-- Used by Alex 2.2 and earlier
alexGetChar input = 
  case inputString input
  of (c:cs) ->
       let pos' = advancePosition c (inputPos input)
       in Just (c, Input cs c pos')
     [] -> Nothing

-- Used by Alex 3.0 and later
alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte input =
  case alexGetChar input
  of Nothing -> Nothing
     Just (c, i) -> Just (fromIntegral $ fromEnum c, i)

alexInputPrevChar input = inputPrevChar input

-- * Lexer actions

type Scanner = Input -> Int -> [T]

-- | A lexer action.  The action takes the remaining input, current startcode,
-- and size of consumed input, and returns a list of tokens.  If an action 
-- does not consume the entire input, it will call the scanner to consume the
-- rest of the input.
--
-- The parameters to @runAction@ are the scanner's continuation, the old
-- input, the new input, the current startcode, and the size of the token to
-- process.
newtype Action =
  Action {runAction :: Scanner -> Input -> Input -> Int -> Int -> [T]}

-- | Output one token
{-# INLINE token #-}
token f = Action $ \scanner old_inp inp sc n ->
  T (inputPos old_inp) (f (inputString old_inp) n) : scanner inp sc

idTok :: Action
idTok = token $ \text n -> interpret $ take n text
  where
    interpret s = let (s1:tags) = splits '\'' s in IdTok s1 tags

    splits c s = case break (c ==) s
                 of (s1, c' : s2) | c == c' -> s1 : splits c s2
                    (s1, [])                -> [s1]

intTok :: Action
intTok = token $ \text n -> IntTok (read $ take n text)

floatTok :: Action
floatTok = token $ \text n -> FltTok (read $ take n text)

stringTok :: Action
stringTok = token $ \text n -> StringTok (read $ take n text)

tok :: Token -> Action
tok t = token $ \_ _ -> t

-- | Consume a CPP line directive.  The directive is used to update the
-- current source position.
lineDirective :: Action
lineDirective = Action $ \scanner old_inp inp sc n ->
  let directive = take n $ inputString old_inp
      inp' = inp {inputPos = source_position directive}
  in scanner inp' sc
  where
    -- The directive reports the line number of the _next_ line.  Subtract
    -- 1 to get the current line.
    source_position directive = fileSourcePos filename (line - 1) 1
      where
        -- Remove the initial '#' from directive
        directive1 = eatSpaces $ tail directive
      
        -- Get line number
        (line, eatSpaces -> directive2):_ = reads directive1
      
        -- Get file name
        (filename, _):_ = reads directive2

    eatSpaces s = dropWhile isSpace s