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
  deriving(Eq, Ord, Show)

-- | Get the foreign language's name as it appears in pyon source code
foreignLanguageName :: ForeignLanguage -> String
foreignLanguageName CCall = "ccall"

-- | A specification of how a symbol is exported to foreign code.  The
-- foreign callign convention and the name visible from foreign code are  
-- given here.
data ExportSpec =
  ExportSpec !ForeignLanguage !String
  deriving(Eq, Ord, Show)

-- | A data type that can be exported to foreign functions.
data ExportDataType =
    -- | A Pyon list.
    --   The list contents can have any monomorphic type.  It's an error
    --   for the list to mention type variables other than constructors.
    ListET Type

    -- | A C array.  The array is passed as a pointer.  The array
    -- size is passed as an additional parameter.
  | CSizeArrayET ExportDataType

    -- | A function type.  Functions are passed as a struct containing a
    --   function object and a pointer to bound variables.
  | FunctionET [ExportDataType] ExportDataType

    -- Plain old data types
  | PyonIntET                   -- ^ Pyon int type
  | PyonFloatET                 -- ^ Pyon float type
  | PyonBoolET                  -- ^ Pyon boolean type
  | PyonComplexFloatET          -- ^ Pyon complex float type
  | CIntET                      -- ^ C int type
  | CFloatET                    -- ^ C float type

instance Show ExportDataType where
  showsPrec prec edt = 
    case edt
    of ListET ty ->
         showParen (prec >= 10) $ 
         showString "ListET (" . shows (pprType ty) . showChar ')'
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
       PyonIntET -> showString "PyonIntET"
       PyonFloatET -> showString "PyonFloatET"
       PyonBoolET -> showString "PyonBoolET"
       PyonComplexFloatET -> showString "PyonComplexFloatET"
       CIntET -> showString "CIntET"
       CFloatET -> showString "CFloatET"

-- | An exported function signature
data ExportSig =
    -- | Exported to other Pyon code.  There's no additional information
    --   because the function contains its Pyon type signature.
    PyonExportSig
    -- | Exported to C.  The C type signature is given here.
  | CExportSig [ExportDataType] ExportDataType
    deriving(Show)