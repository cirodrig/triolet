{-| Descriptions of exported functions.  Information that is stable across 
multiple compiler stages belongs here.  Information specific to a stage is
found in that stage's directory.
-}

module Export where

import Data.List
import Text.Show
import Type.Type

-- | The foreign language to which a name is exported.
data ForeignLanguage =
    CCall
  | CPlusPlus
    deriving(Eq, Ord, Show)

-- | Get the foreign language's name as it appears in triolet source code
foreignLanguageName :: ForeignLanguage -> String
foreignLanguageName CCall = "ccall"
foreignLanguageName CPlusPlus = "cplusplus"

-- | A source code declaration of how a symbol is exported to foreign
-- code.  The foreign calling convention and the name visible from
-- foreign code are specified.  The compiler will draw in other information 
-- to elaborate this into an 'ExportSig'.
data ExportSpec =
  ExportSpec !ForeignLanguage !String
  deriving(Eq, Ord, Show)

-- | A data type that can be exported to foreign functions.
data ExportDataType =
    -- | An N-tuple.
    TupleET [ExportDataType]

    -- | A Triolet list.
    --   The boolean parameter is the boxing of array elements 
    --   (True means boxed, False means unboxed)
  | ListET !Bool ExportDataType

    -- | A Triolet array.
    --   The first parameter is the array dimensionality.
    --   The second parameter is the boxing of array elements 
    --   (True means boxed, False means unboxed)
  | ArrayET !Int !Bool ExportDataType

    -- | A C array.  The array is passed as a pointer.  The array
    -- size is passed as an additional parameter.
  | CSizeArrayET ExportDataType

    -- | A function type.  Functions are passed as a struct containing a
    --   function object and a pointer to bound variables.
  | FunctionET [ExportDataType] ExportDataType

    -- Plain old data types
  | TrioletNoneET                  -- ^ Triolet NoneType type
  | TrioletIntET                   -- ^ Triolet int type
  | TrioletInt64ET                 -- ^ Triolet int64 type
  | TrioletFloatET                 -- ^ Triolet float type
  | TrioletBoolET                  -- ^ Triolet boolean type
  | CIntET                      -- ^ C int type
  | CFloatET                    -- ^ C float type

instance Show ExportDataType where
  showsPrec prec edt = 
    case edt
    of TupleET tys ->
         showParen (prec >= 10) $
         foldr (.) id $ intersperse (showChar ',') $ map shows tys
       ListET b ty ->
         showParen (prec >= 10) $ 
         showString "ListET " . showBoxing b . showChar '(' .
         shows ty . showChar ')'
       ArrayET n b ty ->
         showParen (prec >= 10) $ 
         showString "ArrayET " . shows n . showChar ' ' .
         showBoxing b .
         showString " (" . shows ty . showChar ')'
       CSizeArrayET et ->
         showString "CSizeArrayET " . showsPrec 10 et
       FunctionET params ret ->
         let show_params :: String -> String
             show_params string = foldr ($) string $
                                  intersperse (showString ", ") $
                                  map shows params
         in showParen (prec >= 10) $
            showString "FunctionET (" .
            show_params .
            showString ") -> " .
            shows ret
       TrioletNoneET -> showString "TrioletNoneET"
       TrioletIntET -> showString "TrioletIntET"
       TrioletInt64ET -> showString "TrioletInt64ET"
       TrioletFloatET -> showString "TrioletFloatET"
       TrioletBoolET -> showString "TrioletBoolET"
       CIntET -> showString "CIntET"
       CFloatET -> showString "CFloatET"
    where
      showBoxing :: Bool -> ShowS
      showBoxing False = showString "unboxed "
      showboxing True = showString "boxed "



-- | A language-specific exported function signature
data ExportSig =
    -- | Exported to other Triolet code.
    -- No additional information is required.
    TrioletExportSig
    -- | Exported to C
  | CExportSig !CSignature
    -- | Exported to C++
  | CXXExportSig !CXXSignature
    deriving(Show)

-- | A C export signature includes the C function type
data CSignature = CSignature [ExportDataType] ExportDataType
                deriving(Show)
                        
-- | A C++ export signature includes the C++ function type and the C++
--   function name.  The C++ function will be a wrapper function defined in
--   a C++ header file generated by the compiler.  The actual implementation 
--   will have a name that's automatically generated by the compiler.
data CXXSignature = CXXSignature String [ExportDataType] ExportDataType
                  deriving(Show)
                        