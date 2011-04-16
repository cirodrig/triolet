
module CParser.Parser(parseFile)
where

import qualified Text.ParserCombinators.Parsec as PS
import qualified Text.ParserCombinators.Parsec.Prim as PS

import Text.Parsec.Expr

import Control.Applicative(Applicative(..), (<*), (*>), (<$>), (<**>))
import Control.Monad

import Text.ParserCombinators.Parsec((<|>), (<?>), unexpected, choice,
                                     option, optionMaybe, many, many1, endBy,
                                     sepEndBy, sepBy, sepBy1)

import CParser.AST
import CParser.Lexer
import Common.SourcePos as PySrcPos
import Type.Type(Repr(..))

-- | The parser type
type P a = PS.GenParser Token () a

-- Helper functions to get the character position into a usable form
toParsecSourcePos :: PySrcPos.SourcePos -> PS.SourcePos -> PS.SourcePos
toParsecSourcePos p template =
    flip PS.setSourceName (fj $ PySrcPos.sourceFile p) $
    flip PS.setSourceLine (fj $ PySrcPos.sourceLine p) $
    flip PS.setSourceColumn (fj $ PySrcPos.sourceColumn p) template
    where
      fj (Just x) = x
      fj Nothing  = internalError "Lost source position in parser"

fromParsecSourcePos :: PS.SourcePos -> PySrcPos.SourcePos
fromParsecSourcePos p =
    fileSourcePos (PS.sourceName p) (PS.sourceLine p) (PS.sourceColumn p)

nextPosition parsec_p _ (Token p _:_) = toParsecSourcePos p parsec_p
nextPosition parsec_p (Token p _) _   = toParsecSourcePos p parsec_p

internalError :: String -> a
internalError msg = error $ "Internal error:\n" ++ msg

-------------------------------------------------------------------------------
-- * Primitive parsers

-- | Succeed iff the specified token appears next in the input stream.
match :: Tok -> P ()
match t = PS.tokenPrim showToken nextPosition matchAndReturn
    where
      matchAndReturn (Token _ t')
          | t == t'   = Just ()
          | otherwise = Nothing

-- | Return the identifier name that appears next in the input stream; fail if
-- not an identifier.
identifier :: P String
--identifier = undefined
identifier = PS.tokenPrim showToken nextPosition matchAndReturn
    where
      matchAndReturn (Token _ (IdentTok s)) = Just s
      matchAndReturn _                      = Nothing

-- | Return the operator name that appears next in the input stream; fail if
-- not an operator.
operator :: P String
operator = PS.tokenPrim showToken nextPosition matchAndReturn
    where
      matchAndReturn (Token _ (OperTok s)) = Just s
      matchAndReturn _                     = Nothing

-- | Return the integer that appears next in the input stream; fail if
-- not an integer.
int :: P Integer
int = PS.tokenPrim showToken nextPosition matchAndReturn
    where
      matchAndReturn (Token _ (IntTok n)) = Just n
      matchAndReturn _                    = Nothing

float :: P Double
float = PS.tokenPrim showToken nextPosition matchAndReturn
    where
      matchAndReturn (Token _ (FloatTok n)) = Just n
      matchAndReturn _                    = Nothing

eof :: P ()
eof = PS.getInput >>= acceptEOF
    where
      acceptEOF []    = return ()
      acceptEOF (x:_) = unexpected (showToken x) <?> "end of file"

-- Matched Parentheses
parens :: P a -> P a
parens = PS.between (match LParenTok) (match RParenTok)

-- Matched brackets
brackets :: P a -> P a
brackets = PS.between (match LBracketTok) (match RBracketTok)

semi :: P ()
semi = match SemiTok

after :: P terminator -> P b -> P b
q `after` p = p <* q

(<*#) :: P a -> Tok -> P a
p <*# t = p <* match t

atsign :: P String
atsign = PS.tokenPrim showToken nextPosition matchAndReturn
    where
      matchAndReturn (Token _ (OperTok "@")) = Just "@"
      matchAndReturn _                     = Nothing
      
doublestar :: P String
doublestar = PS.tokenPrim showToken nextPosition matchAndReturn
    where
      matchAndReturn (Token _ (OperTok "**")) = Just "**"
      matchAndReturn _                     = Nothing  


literal :: P Lit
literal = fmap IntL int <|>
          fmap FloatL float
        
representation :: P Repr
representation = (match ValTok >> return Value) <|>
                 (match BoxTok >> return Boxed) <|>
                 (match RefTok >> return Referenced)

-- match the corresponding Repr Token
returnRepr :: P ReturnRepr
returnRepr = choice [match tok >> return repr | (tok, repr) <- reprs]
  where
    reprs = [(ValTok, ValueRT), (BoxTok, BoxedRT),
             (ReadTok, ReadRT), (WriteTok, WriteRT),
             (OutTok, OutRT), (SideEffectTok, SideEffectRT)]

-- match the corresponding Repr Token.  Doesn't match dependent parameters.
paramRepr :: P (ParamRepr Parsed)
paramRepr = choice [match tok >> return repr | (tok, repr) <- reprs]
  where
    reprs = [(ValTok, ValuePT Nothing), (BoxTok, BoxedPT),
             (ReadTok, ReadPT), (WriteTok, WritePT),
             (OutTok, OutPT), (SideEffectTok, SideEffectPT)]

-------------------------------------------------------------------------------
-- * Derived parsers



-- Keep parsing, separated by Semicolons, until EOF
myParseComp :: P [(LDecl Parsed)]
myParseComp = eof `after` (topDecl `sepEndBy` semi)


parseModule :: P PModule
parseModule = do dList <- myParseComp
                 return $ Module dList

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

locatePosition = fmap fromParsecSourcePos PS.getPosition


located :: P t -> P (Located t)
located p = do
 -- Get the current source position
 loc <- fmap fromParsecSourcePos PS.getPosition
 -- Parse a 't', by running the parser you received
 unloc <- p
 -- Put the position and 't' into a 'Located t'
 return $ L loc unloc
 

topDecl :: P (LDecl Parsed)
topDecl = located (var_decl <|> datatype_decl) 
  where
    var_decl = do
      declVar <- identifier
      match ColonTok 
      declType <- anyReturnType
      return $ VarDecl declVar declType Nothing

    datatype_decl = do
      match DataTok
      repr <- representation
      declVar <- identifier
      match ColonTok 
      declType <- anyReturnType
      match LBraceTok
      cons <- dataConDecl `sepEndBy` match SemiTok
      match RBraceTok
      return $ DataDecl declVar repr declType cons

dataConDecl = located $ do
  declVar <- identifier
  match ColonTok
  declType <- anyReturnType
  match CommaTok
  params <- parens $ anyParamT `sepBy` match CommaTok -- Forall types
  ex_params <- parens $ anyParamT `sepBy` match CommaTok -- Existential types
  args <- parens $ anyReturnType `sepBy` match CommaTok     -- Fields
  match ColonTok
  rng <- anyReturnType
  return $ DataConDecl declVar declType params ex_params args rng

-------------------------------------------------------------------------------
-- Type parsing

-- Parse any return type.
-- Function types are boxed if no representation is given.
-- This is not used to parse a subexpression of a type.
anyReturnType :: P (ReturnType Parsed)
anyReturnType = returnType (Just BoxedRT)

-- No restrictions on what comes next in the token stream
anyPType :: Maybe ReturnRepr -> P (LType Parsed)
anyPType implicit_rrepr =
   -- This first case is here to propagate implicit_rrepr through parentheses
  PS.try (parens (anyPType implicit_rrepr)) <|>
  PS.try (funT implicit_rrepr) <|>
  appType

-- A type application or tighter-binding term.  The implicit return
-- representation is used if the term is a parenthesized function.
appPType :: Maybe ReturnRepr -> P (LType Parsed)
appPType implicit_rrepr =
  PS.try (parens (anyPType implicit_rrepr)) <|> appType

-- A type application or tighter-binding term.  There's no implicit return
-- representation.
appType :: P (LType Parsed)
appType = do
  pos <- locatePosition
  head <- distPType
  lst <- many distPType -- If head is followed by more types, it's an application
  if null lst
    then return head
    else return $ L pos (AppT head lst)

-- A variable or parenthesized type
distPType :: P (LType Parsed)
distPType = parse_var <|> parens (anyPType Nothing)
  where
    parse_var = located (VarT <$> identifier)

-- Match a function type.  The function's return representation may be
-- implicitly determined by the context in which this type appears.
funT :: Maybe ReturnRepr -> P (LType Parsed)
funT implicit_rrepr = located $ do
  param <- paramT
  match ArrowTok
  range <- returnType implicit_rrepr
  return $ FunT param range

-- Parse a return type.  This consists of a representation followed by a type.
-- If the parsing context implicitly determines a representation, then the
-- representation is optional.
returnType implicit_rrepr = implicit_multi_return <|> single_return
  where
    -- The range is a function without an explicit representation.  Give the
    -- range the same representation that this function has.
    implicit_multi_return =
      case implicit_rrepr
      of Nothing -> PS.pzero
         Just r  -> ReturnType r <$> PS.try (funT implicit_rrepr)

    -- The range has an explicit representation, followed by a type
    single_return = do
      rrepr <- returnRepr 
      rtype <- anyPType (Just rrepr)
      return $ ReturnType rrepr rtype

-- A parser for any parameter type
anyParamT :: P (ParamType Parsed)
anyParamT = val_param <|> readParamT anyPType <|> parens anyParamT
  where
    val_param = match ValTok >> (PS.try dep <|> nondep)
      where
        dep = do
          v <- identifier
          match ColonTok
          ty <- anyPType (Just ValueRT)
          return $ ParamType (ValuePT (Just v)) ty
        
        nondep = do
          ty <- anyPType (Just ValueRT)
          return $ ParamType (ValuePT Nothing) ty

-- A parser for parameter types that don't bind a variable
paramT = readParamT appPType <|> parens anyParamT

readParamT read_type = do
  repr <- paramRepr
  ty <- read_type (Just $ as_return_repr repr)
  return $ ParamType repr ty
  where
    as_return_repr (ValuePT _) = ValueRT
    as_return_repr BoxedPT = BoxedRT
    as_return_repr ReadPT = ReadRT
    as_return_repr WritePT = WriteRT
    as_return_repr OutPT = OutRT
    as_return_repr SideEffectPT = SideEffectRT

{-
expr = buildExpressionParser table appType

table = [ [binOp "@" handleAt AssocNone]
        , [binOp "**" handleDStar AssocRight]
        ]

binOp name fun assoc = Infix (do {resOp name; return fun}) assoc
resOp s = 
  case s of
    "@" -> atsign
    "**" -> doublestar

-- | Create a variable with the Gluon name
handleAt :: (LType Parsed)-> (LType Parsed) -> (LType Parsed)
handleAt a b =
  case (a,b) of
    (L pos1 x, L pos2 y) -> (L pos1 (AppT (L pos2 (VarT "AtE")) [a,b]))
    
-- | Create a variable with the Gluon name
handleDStar :: (LType Parsed)-> (LType Parsed) -> (LType Parsed)
handleDStar a b = case (a,b)
  of (L pos1 x, L pos2 y) -> (L pos1 (AppT (L pos2 (VarT "SconjE")) [a,b]))
-}

-------------------------------------------------------------------------------
-- * Entry point

-- | Parse a sequence of tokens.  Returns an AST.
--parseFile :: FilePath -> [Token] -> IO PModule
parseFile :: FilePath -> [Token] -> IO PModule
parseFile path tokens =
  case PS.runParser parseModule () path tokens
  of Left err -> do
       print err
       fail "Parsing failed"
     Right m -> do
       return m
       
------------------------------------------------------------------

