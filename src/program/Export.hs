{-| Descriptions of exported functions.  Information that is stable across 
multiple compiler stages belongs here.  Information specific to a stage is
found in that stage's directory.
-}

module Export where

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
    -- | A Pyon list
    ListET ExportDataType
    -- | A C array.  The array is passed as a pointer.  The array
    -- size is passed as an additional parameter.
  | CSizeArrayET ExportDataType

    -- Plain old data types
  | PyonIntET                   -- ^ Pyon int type
  | PyonFloatET                 -- ^ Pyon float type
  | PyonBoolET                  -- ^ Pyon boolean type 
  | CIntET                      -- ^ C int type
  | CFloatET                    -- ^ C float type

-- | An exported function signature
data ExportSig = ExportSig [ExportDataType] ExportDataType
    