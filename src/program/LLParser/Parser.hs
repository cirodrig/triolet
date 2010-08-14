
module LLParser.Parser where

import Control.Monad
import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Pos as Parsec
import Text.ParserCombinators.Parsec.Expr

import qualified Gluon.Common.SourcePos
import LowLevel.Types
import LLParser.Lexer
import LLParser.AST

type P a = GenParser T () a

toParsecPos :: Gluon.Common.SourcePos.SourcePos -> Parsec.SourcePos
toParsecPos pos =
  let Just filename = Gluon.Common.SourcePos.sourceFile pos 
      Just line = Gluon.Common.SourcePos.sourceLine pos
      Just col = Gluon.Common.SourcePos.sourceColumn pos
  in Parsec.newPos filename line col

fromParsecPos :: Parsec.SourcePos -> Gluon.Common.SourcePos.SourcePos
fromParsecPos pos =
  let filename = Parsec.sourceName pos 
      line = Parsec.sourceLine pos
      col = Parsec.sourceColumn pos
  in Gluon.Common.SourcePos.fileSourcePos filename line col

tPos (T pos _) = pos
tToken (T _ t) = t

nextParsecPos _ _ (t:_) = toParsecPos $ tPos t
nextParsecPos _ t []    = toParsecPos $ tPos t

{-followedByOneOf :: P a -> [Token] -> P a
p `followedByOneOf` toks = do
  x <- p
  case getInput
    of t:_ | any (tToken t ==) toks -> return x
       _ -> pzero-}

matchAny :: [Token] -> P ()
matchAny ts = tokenPrim showT nextParsecPos match_any
  where
    match_any t' | any (tToken t' ==) ts = Just ()
                 | otherwise = Nothing

match :: Token -> P ()
match t = tokenPrim showT nextParsecPos match_token <?> showToken t
  where
    match_token t' | t == tToken t' = Just ()
                   | otherwise      = Nothing

identifier :: P String
identifier = tokenPrim showT nextParsecPos get_identifier
  where
    get_identifier t = case tToken t
                       of IdTok s -> Just s
                          _ -> Nothing

integer :: P Integer
integer = tokenPrim showT nextParsecPos get_int
  where
    get_int t = case tToken t
                of IntTok n -> Just n
                   _ -> Nothing

floating :: P Double
floating = tokenPrim showT nextParsecPos get_int
  where
    get_int t = case tToken t
                of FloatTok n -> Just n
                   _ -> Nothing

parens :: P a -> P a
parens p = do
  match LParenTok
  x <- p
  match RParenTok
  return x

parenList :: P a -> P [a]
parenList p = parens $ p `sepBy` match CommaTok

braces :: P a -> P a
braces p = do
  match LBraceTok
  x <- p
  match RBraceTok
  return x

-- | Override the default Show behavior of 'String'
newtype ShowString = ShowString String

instance Show ShowString where show (ShowString s) = s

endOfFile :: P ()
endOfFile = notFollowedBy $ tokenPrim showT nextParsecPos anything
  where
    anything t = Just $ ShowString $ showT t

-------------------------------------------------------------------------------

parseType :: P (Type Parsed)
parseType = prim_type <|> record_type <|> bytes_type <?> "type"
  where
    prim_type = choice [match tok >> return (PrimT typ)
                       | (tok, typ) <- primtypes]
    primtypes = [ (Int8Tok, IntType Signed S8)
                , (Int16Tok, IntType Signed S16)
                , (Int32Tok, IntType Signed S32)
                , (Int64Tok, IntType Signed S64)
                , (UInt8Tok, IntType Unsigned S8)
                , (UInt16Tok, IntType Unsigned S16)
                , (UInt32Tok, IntType Unsigned S32)
                , (UInt64Tok, IntType Unsigned S64)
                , (OwnedTok, OwnedType)
                , (PointerTok, PointerType)]

    record_type = fmap RecordT identifier

    bytes_type = match BytesTok >> parens (liftM2 BytesT expr expr)

field :: P (Field Parsed)
field = do
  liftM3 Field identifier fields cast <?> "field offset specifier"
  where
    fields = many1 (match DotTok >> identifier) <?> "field specifiers"
    cast = optionMaybe (match AsTok >> parseType)

-- | Operators recognized by the parser
operators =
  [ [ Infix (binaryOp DerefPlusTok AtomicAddOp) AssocNone]
  , [ Infix (binaryOp EqualTok CmpEQOp) AssocNone]
  ]
  where
    binaryOp tok op = match tok >> return (\x y -> BinaryE op x y)

expr = buildExpressionParser operators fieldExpr

fieldExpr :: P (Expr Parsed)
fieldExpr = do
  e <- castExpr
  postfixes e
  where
    postfixes e =
      (match AtTok >> offset_expr e >>= postfixes) <|>
      (match FieldTok >> deref_expr e >>= postfixes) <|>
      return e

    -- Parse the rest of an offset expression "e @ field"
    offset_expr e = do
      f <- field
      return $ FieldE e f
    
    -- Parse the rest of a dereference expression "e @! field"
    deref_expr e = do
      f <- field
      return $ LoadFieldE e f

castExpr :: P (Expr Parsed)
castExpr = do
  e <- basicExpr
  choice [ match AsTok >> cast_expr e
         , return e
         ]
  where
    cast_expr e = do
      ty <- parseType
      return $ CastE e ty

-- Match expressions that start with an identifier or literal type.
basicExpr :: P (Expr Parsed)
basicExpr =
  sizeof_expr <|> alignof_expr <|>
  (identifier >>= basicExprWithIdentifier) <|>
  (parseType >>= basicExprWithType) <|>
  try (parenList parseType >>= basicExprWithTypes) <|>
  atomicExpr
  where
    sizeof_expr = do
      match SizeofTok 
      fmap SizeofE parseType
    alignof_expr = do
      match AlignofTok 
      fmap SizeofE parseType

-- Parse an expression that began with an identifier 
basicExprWithIdentifier id =
  recordE <|> try (basicExprWithType (RecordT id)) <|> varE
  where
    recordE = try $ do
      RecordE id `liftM` braces (expr `sepBy` match CommaTok)
    
    varE = return $ VarE id

-- | Parse an expression that began with a type.
basicExprWithType ty = intLitE <|> floatLitE <|> basicExprWithTypes [ty]
  where
    intLitE = fmap (IntLitE ty) integer
    
    floatLitE = fmap (FloatLitE ty) floating

-- | Parse an expression that begain with a type list.
basicExprWithTypes tys = callE
  where
    callToken = (match CallTok >> return (CallE tys)) <|>
                (match PrimCallTok >> return (PrimCallE tys))

    callE = callToken `ap` atomicExpr `ap` atomicExprList

atomicExprList = parenList expr <|> fmap (:[]) atomicExpr

-- | An atomic expression.  Expressions are atomic if they are not made of 
-- parts separated by spaces.
atomicExpr = fmap VarE identifier <|> parens expr

-- | An lvalue is parsed as an expression, then converted to an lvalue if
-- it appears in lvalue context.
-- This consumes no input, but may cause a parse error.
exprToLValue :: Expr Parsed -> P (LValue Parsed)
exprToLValue (VarE v) = return $ VarL v
exprToLValue (LoadFieldE base off) = return $ StoreFieldL base off
exprToLValue _ = fail "LHS of assignment is not an lvalue"

-- | An expression list found in a statement.
-- To resolve ambiguity, the expression list must be followed by an equal
-- sign or semicolon.
stmtExprList = try (fmap (:[]) expr) <|> parenList expr

atom :: P (Atom Parsed)
atom = otherAtom <|> fmap ValA stmtExprList

otherAtom = if_atom
  where
    if_atom = do
      match IfTok
      cond <- parens expr
      if_true <- block
      match ElseTok
      if_false <- block
      return $ IfA cond if_true if_false

-- | Parse a block of statements
block :: P (Block Parsed)
block = braces statements
  where
    statements = other_atom <|> let_or_atom

    -- An atom that doesn't appear on the RHS of an assignment ends the
    -- statement
    other_atom = do
      a <- otherAtom
      match SemiTok
      return $ Block [] a

    -- A statement starting with an expression list: either assignment or
    -- the end of the block
    let_or_atom = do
      es <- stmtExprList
      (match AssignTok >> assign_lvalues es) <|> end_block es
    
    -- Create an assignment statement (LHS = RHS; ...)
    assign_lvalues es = do
      lvalues <- mapM exprToLValue es
      rhs <- atom
      match SemiTok
      Block stmts val <- statements
      return $ Block (LetS lvalues rhs : stmts) val
    
    end_block es = do
      match SemiTok
      return $ Block [] (ValA es)

-------------------------------------------------------------------------------
-- Definitions

parameter :: P (Parameter Parsed)
parameter = liftM2 Parameter parseType identifier

parameters :: P (Parameters Parsed)
parameters = parenList parameter

recordDef :: P (RecordDef Parsed)
recordDef = do
  match RecordTok
  name <- identifier
  params <- option [] parameters
  fields <- braces $ fieldDef `sepEndBy` match SemiTok
  return $ RecordDef name params fields

fieldDef :: P (FieldDef Parsed)
fieldDef = liftM2 FieldDef parseType identifier

dataDef :: P (DataDef Parsed)
dataDef = do
  match DataTok
  
  -- Read a type, which must be 'owned' or 'pointer'
  data_type <- parseType
  ty <- case data_type of 
    PrimT OwnedType -> return OwnedType
    PrimT PointerType -> return PointerType
    _ -> fail "type must be 'owned' or 'pointer'"

  name <- identifier
  match AssignTok
  value <- expr
  return $ DataDef name ty value

-- | Parse a function or procedure definition
functionDef :: P (FunctionDef Parsed)
functionDef = do
  is_procedure <- choice [ match FunctionTok >> return False 
                         , match ProcedureTok >> return True]
  name <- identifier
  params <- parameters
  match ArrowTok
  returns <- fmap (:[]) parseType <|> parenList parseType
  body <- block
  return $ FunctionDef name is_procedure params returns body

topLevelDefs :: P [Def Parsed]
topLevelDefs = do defs <- def `sepEndBy` match SemiTok
                  endOfFile
                  return defs
  where
    def = choice [ fmap FunctionDefEnt functionDef
                 , fmap DataDefEnt dataDef
                 , fmap RecordDefEnt recordDef]

-------------------------------------------------------------------------------

-- | Test the parser on a string.  For debugging.
testParse :: String -> P a -> a
testParse text parser =
  let tokens = lexFile "<test>" text
  in case runParser parser () "<test>" tokens
     of Left err -> error (show err)
        Right x -> x

parseFile :: FilePath -> String -> IO [Def Parsed]
parseFile path text =
  let tokens = lexFile path text
  in case runParser topLevelDefs () path tokens
     of Left err -> fail (show err)
        Right x -> return x