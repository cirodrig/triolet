
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
             (ReadTok, ReadRT), (WriteTok, WriteRT)]

-- match the corresponding Repr Token.  Doesn't match dependent parameters.
paramRepr :: P (ParamRepr Parsed)
paramRepr = choice [match tok >> return repr | (tok, repr) <- reprs]
  where
    reprs = [(ValTok, ValuePT Nothing), (BoxTok, BoxedPT),
             (ReadTok, ReadPT), (WriteTok, WritePT)]

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
      declType <- returnType
      return $ VarDecl declVar declType

    datatype_decl = do
      match DataTok
      repr <- representation
      declVar <- identifier
      match ColonTok 
      declType <- returnType
      match LBraceTok
      cons <- dataConDecl `sepEndBy` match SemiTok
      match RBraceTok
      return $ DataDecl declVar repr declType cons

dataConDecl = located $ do
  declVar <- identifier
  match ColonTok
  declType <- returnType
  match CommaTok
  params <- parens $ anyParamT `sepBy` match CommaTok
  args <- parens $ returnType `sepBy` match CommaTok
  match ColonTok
  rng <- returnType
  return $ DataConDecl declVar declType params args rng

-- No restrictions on what comes next in the token stream
anyPType :: P PType
anyPType = PS.try funT <|> readAppVarT

-- Distinct P Types, no Application or Functions, only singular VarT, or guarded terms       
distPType :: P PType
distPType = readVarT <|> parens anyPType

-- Use to get the head of an Application.  No Literal. Allowing parentheses case for lambda types
headAppPType :: P PType
headAppPType = readVarT <|> parens anyPType

-- Make a VarT with an expected Identifier
readVarT :: P PType
readVarT = fmap VarT identifier

-- Match a function, in particular, the ArrowTok
funT :: P PType
funT = do 
  param <- paramT
  match ArrowTok
  range <- returnType
  return $ FunT param range

-- A parser for any parameter type
anyParamT :: P (ParamType Parsed)
anyParamT = val_param <|> readParamT anyPType <|> parens anyParamT
  where
    val_param = match ValTok >> (PS.try dep <|> nondep)
      where
        dep = do
          v <- identifier
          match ColonTok
          ty <- located anyPType
          return $ ParamType (ValuePT (Just v)) ty
        
        nondep = do
          ty <- located anyPType
          return $ ParamType (ValuePT Nothing) ty

-- A parser for parameter types that don't bind a variable
paramT = readParamT readAppVarT <|> parens anyParamT

readParamT read_type = do
  repr <- paramRepr
  ty <- located read_type
  return $ ParamType repr ty

-- Find the Type of a function's return type
returnType :: P (ReturnType Parsed)
returnType = PS.try multiReturn <|>
             PS.try implicitMultiReturn <|>
             singleReturn

-- We've already started a function, but we might be curried into another function's parameter.  Eventually, something will become this ReturnType's type
-- of the form " [after Function ->] val int -> val int"
implicitMultiReturn :: P (ReturnType Parsed)
implicitMultiReturn = do
  ft <- located funT
  return $ ReturnType BoxedRT ft

-- ReturnType with another function curried
-- of the form " [after Function ->] val val int -> val int", with both keywords explicit
multiReturn :: P (ReturnType Parsed)
multiReturn = do
  rtRepr <- returnRepr
  ft <- located funT
  return $ ReturnType rtRepr ft

-- Just a plain ReturnType, no currying
singleReturn :: P (ReturnType Parsed)
singleReturn =
  do rtRepr <- returnRepr
     rtType <- located readAppVarT
     return $ ReturnType rtRepr rtType
                                     
-- Traverse down productions to keep associativity and precendence
-- Eventually boils down to either AppT, a single VarT, or a parenthesis-guarded Type of any kind                                     
readAppVarT :: P PType
readAppVarT = do
  s <- expr
  return $ unLoc s

atomicAppVarT :: P (LType Parsed)
atomicAppVarT = do
  pos <- locatePosition
  head <- located headAppPType
  lst <- optionMaybe( (many1 (located distPType)))
  case lst of
    Nothing  -> return head
    Just args -> return $ L pos (AppT head args)

expr = buildExpressionParser table atomicAppVarT

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

