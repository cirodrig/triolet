
module LLParser.Parser(parseFile)
where

import Control.Monad
import Data.List
import Text.ParserCombinators.Parsec hiding(string)
import qualified Text.ParserCombinators.Parsec.Pos as Parsec
import Text.ParserCombinators.Parsec.Expr

import Gluon.Common.Label
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

string :: P String
string = tokenPrim showT nextParsecPos get_string
  where
    get_string t = case tToken t
                        of StringTok s -> Just s
                           _ -> Nothing

parseModuleName :: P ModuleName
parseModuleName = do
  components <- identifier `sepBy1` match DotTok
  return $ moduleName $ intercalate "." components

fullyQualifiedName :: P Label
fullyQualifiedName = do
  components <- identifier `sepBy1` match DotTok
  unless (length components >= 2) $ fail "must provide a fully-qualified name"
  let mod = moduleName (intercalate "." $ init components)
  return $ pgmLabel mod (last components)

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
    primtypes = [ (BoolTok, BoolType)
                , (Int8Tok, IntType Signed S8)
                , (Int16Tok, IntType Signed S16)
                , (Int32Tok, IntType Signed S32)
                , (Int64Tok, IntType Signed S64)
                , (UInt8Tok, IntType Unsigned S8)
                , (UInt16Tok, IntType Unsigned S16)
                , (UInt32Tok, IntType Unsigned S32)
                , (UInt64Tok, IntType Unsigned S64)
                , (OwnedTok, OwnedType)
                , (PointerTok, PointerType)]

    record_type = do
      rt <- fmap RecordT identifier
      try (type_app rt) <|> return rt
      where
        type_app rt = do
          args <- parenList parseType
          return $ AppT rt args

    bytes_type = do
      match BytesTok 
      parens $ do 
        sz <- expr
        match CommaTok
        al <- expr
        return $ BytesT sz al

-- | Parse a type of a global object.  The only valid types
-- are \'owned\' or \'pointer\'.
parseGlobalType :: P PrimType
parseGlobalType = owned_type <|> pointer_type <?> "'owned' or 'pointer' type"
  where
    owned_type = match OwnedTok >> return OwnedType
    pointer_type = match PointerTok >> return PointerType

field :: P (Field Parsed)
field = do
  liftM3 Field identifier fields cast <?> "field offset specifier"
  where
    fields = many1 (match DotTok >> identifier) <?> "field specifiers"
    cast = optionMaybe (match AsTok >> parseType)

-- | Operators recognized by the parser
operators =
  [ [ Infix (binaryOp StarTok MulOp) AssocLeft
    , Infix (binaryOp PercentTok ModOp) AssocNone]
  , [ Prefix (unaryOp MinusTok NegateOp)]
  , [ Infix (binaryOp DerefPlusTok AtomicAddOp) AssocNone
    , Infix (binaryOp PointerPlusTok PointerAddOp) AssocLeft
    , Infix (binaryOp PlusTok AddOp) AssocLeft
    , Infix (binaryOp MinusTok SubOp) AssocLeft]
  , [ Infix (binaryOp EqualTok CmpEQOp) AssocNone
    , Infix (binaryOp NotEqualTok CmpNEOp) AssocNone]
  ]
  where
    binaryOp tok op = match tok >> return (\x y -> BinaryE op x y)
    unaryOp tok op = match tok >> return (\x -> UnaryE op x)

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
  derefExpr
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
basicExprWithType ty =
  intLitE <|> floatLitE <|> loadE <|> basicExprWithTypes [ty]
  where
    intLitE = fmap (IntLitE ty) integer
    
    floatLitE = fmap (FloatLitE ty) floating

    loadE = do
      match LoadTok
      addr <- derefExpr
      return $ LoadE ty addr

-- | Parse an expression that begain with a type list.
basicExprWithTypes tys = callE
  where
    callToken = (match CallTok >> return (CallE tys)) <|>
                (match PrimCallTok >> return (PrimCallE tys))

    callE = callToken `ap` derefExpr `ap` derefExprList

derefExprList = parenList expr <|> fmap (:[]) derefExpr

derefExpr = deref <|> atomicExpr
  where
    deref = do
      match DerefTok
      e <- atomicExpr
      return $ DerefE e

-- | An atomic expression.  Expressions are atomic if they are not made of 
-- parts separated by spaces.
atomicExpr = fmap VarE identifier <|> true_lit <|> false_lit <|> null_lit <|>
             wild <|> parens expr
  where
    true_lit = match TrueTok >> return (BoolLitE True)
    false_lit = match FalseTok >> return (BoolLitE False)
    null_lit = match NullTok >> return NullLitE
    wild = match WildTok >> return WildE

-- | An lvalue is parsed as an expression, then converted to an lvalue if
-- it appears in lvalue context.
-- This consumes no input, but may cause a parse error.
exprToLValue :: Expr Parsed -> P (LValue Parsed)
exprToLValue (VarE v) = return $ VarL v
exprToLValue (DerefE e) = return $ StoreL e
exprToLValue (LoadFieldE base off) = return $ StoreFieldL base off
exprToLValue (RecordE rec fields) =
  fmap (UnpackL rec) $ mapM exprToLValue fields
exprToLValue WildE = return $ WildL
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

-- | Parse a list of type parameters
recordParameters :: P [String]
recordParameters = parenList identifier

recordDef :: P (RecordDef Parsed)
recordDef = do
  match RecordTok
  name <- identifier
  params <- option [] recordParameters
  fields <- braces $ fieldDef `sepEndBy` match SemiTok
  return $ RecordDef name params fields

fieldDef :: P (FieldDef Parsed)
fieldDef = liftM2 FieldDef parseType identifier

dataDef :: P (DataDef Parsed)
dataDef = do
  match DataTok
  
  -- Read a type, which must be 'owned' or 'pointer'
  data_type <- parseGlobalType

  name <- identifier
  match AssignTok
  value <- expr
  return $ DataDef name data_type value

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
-- Module parsing

externDecl :: P (ExternDecl Parsed)
externDecl = extern_decl <|> import_decl
  where
    extern_decl = do
      match ExternTok
      extern_type <- parseGlobalType
      label <- fullyQualifiedName
      c_name <- optionMaybe string
      return $ ExternDecl extern_type label c_name

    import_decl = do
      match ImportTok
      extern_type <- parseGlobalType
      local_name <- identifier
      c_name <- option local_name string
      return $ ImportDecl extern_type c_name local_name

parseModule :: P (ModuleName, [ExternDecl Parsed], [Def Parsed])
parseModule = do
  -- Parse the module name declaration
  match ModuleTok
  mn <- parseModuleName
  match SemiTok
  
  -- Parse 'extern' declarations
  exts <- externDecl `sepEndBy` match SemiTok
  
  -- Parse definitions
  defs <- topLevelDefs
  
  return (mn, exts, defs)

-------------------------------------------------------------------------------

-- | Test the parser on a string.  For debugging.
testParse :: String -> P a -> a
testParse text parser =
  let tokens = lexFile "<test>" text
  in case runParser parser () "<test>" tokens
     of Left err -> error (show err)
        Right x -> x

parseFile :: FilePath -> String
          -> IO (ModuleName, [ExternDecl Parsed], [Def Parsed])
parseFile path text =
  let tokens = lexFile path text
  in case runParser parseModule () path tokens
     of Left err -> fail (show err)
        Right x -> return x