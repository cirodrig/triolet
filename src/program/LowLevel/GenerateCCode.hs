{-| Helper functions for generating C code. 
-}

module LowLevel.GenerateCCode where

import Gluon.Common.Error

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Pretty
import Language.C.Syntax.AST
import Language.C.Syntax.Constants

import LowLevel.Builtins
import LowLevel.Label
import LowLevel.Types
import LowLevel.Record
import LowLevel.Syntax
import LowLevel.Print
import LowLevel.GenerateCUtils

-------------------------------------------------------------------------------
-- Declarations, literals, and values

-- | Define an unitialized piece of global data.
declareBytes :: Var -> Int -> Int -> CDecl
declareBytes v size align =
  let array = CArrDeclr [] (CArrSize False $ smallIntConst size) internalNode
      align_expr = smallIntConst align
      align_attr = CAttr (builtinIdent "aligned") [align_expr] internalNode
      ident = varIdent v
      declr = CDeclr (Just ident) [array] Nothing [align_attr] internalNode
      type_spec = CTypeSpec (CCharType internalNode)
  in CDecl [type_spec] [(Just declr, Nothing, Nothing)] internalNode

-- | Declare or define a variable.  The variable is not global and
--   is not accessed by reference.
declareLocalVariable :: Var -> Maybe CExpr -> CDecl
declareLocalVariable v initializer =
  let (type_specs, derived_declr) = primTypeDeclSpecs $ varPrimType v
      ident = localVarIdent v
      declr = CDeclr (Just ident) derived_declr Nothing [] internalNode
      init = case initializer
             of Nothing -> Nothing
                Just e  -> Just $ CInitExpr e internalNode
  in CDecl type_specs [(Just declr, init, Nothing)] internalNode

-- | Declare a local variable with no initial value.
declareUndefLocalVariable :: Var -> CDecl
declareUndefLocalVariable v = declareLocalVariable v Nothing

-- | The type of a @PyonPtr@, used in type casts.
pyonPointerType :: CDecl
pyonPointerType = anonymousDecl (nameDeclSpecs "PyonPtr")

-- | Generate a constant integer expression
intConst :: Integral a => Signedness -> Size -> a -> CExpr
intConst sgn sz n =
  let sign_flag = case sgn
                  of Signed -> ""
                     Unsigned -> "U"     
      size_flag = case sz
                  of S64 -> "L"
                     _ -> ""
      read_int m =
        case readCInteger DecRepr (show m ++ sign_flag ++ size_flag)
        of Left _ -> internalError "genLit: Cannot generate integer literal"
           Right x -> x
      
      -- If the literal is negative, then generate a positive literal and then
      -- negate it
      literal = CConst $ CIntConst (read_int $ abs n) internalNode
  in if n >= 0
     then literal
     else CUnary CMinOp literal internalNode

smallIntConst :: Int -> CExpr
smallIntConst n = intConst Signed nativeIntSize n

floatConst :: Size -> Double -> CExpr
floatConst _ n =
  let literal = CConst $ CFloatConst (readCFloat (show $ abs n)) internalNode
  in if n >= 0
     then literal
     else CUnary CMinOp literal internalNode

-- | A NULL pointer
nullPtr :: CExpr
nullPtr =
  let declr = anonymousDecl $ ptrDeclSpecs voidDeclSpecs
  in CCast declr (smallIntConst 0) internalNode

-- | Cast an expression to the C equivalent of a pointer to the given type
cCast :: PrimType -> CExpr -> CExpr
cCast to_type expr =
  let decl = anonymousDecl $ ptrDeclSpecs $ primTypeDeclSpecs to_type
  in CCast decl expr internalNode

-- | Cast an expression to PyonPtr type
cPtrCast :: CExpr -> CExpr
cPtrCast expr = CCast pyonPointerType expr internalNode

-- | Generate a pointer offset expression.
--   The generated expression is a call to PYON_OFF (actually a macro) 
--   with the pointer and offset
offset :: CExpr -> CExpr -> CExpr
offset base off 
  | isZeroCExpr off = base
  | otherwise =
      CCall (CVar (internalIdent "PYON_OFF") internalNode) [base, off]
      internalNode

isZeroCExpr :: CExpr -> Bool
isZeroCExpr e =
  case e
  of CConst (CIntConst n _) -> getCInteger n == 0
     _ -> False

cVar var_ident = CVar var_ident internalNode

cUnary :: CUnaryOp -> CExpr -> CExpr
cUnary op e = CUnary op e internalNode

cBinary :: CBinaryOp -> CExpr -> CExpr -> CExpr
cBinary op e f = CBinary op e f internalNode

cCond :: CExpr -> CExpr -> CExpr -> CExpr
cCond c t f = CCond c (Just t) f internalNode

cAssign :: CExpr -> CExpr -> CExpr
cAssign lhs rhs = CAssign CAssignOp lhs rhs internalNode

cCall :: CExpr -> [CExpr] -> CExpr
cCall op args = CCall op args internalNode

cEmptyStat :: CStat
cEmptyStat = CExpr Nothing internalNode

cExprStat :: CExpr -> CStat
cExprStat e = CExpr (Just e) internalNode

cGoto :: Ident -> CStat
cGoto lab = CGoto lab internalNode