-- | The TH functions in this module automate the task of creating large, 
-- single-constructor, record data types.
--
-- To use this module, first create a /specification/ module that exports 
-- a data type specification.  Then create an /implementation/ module that
-- declares the data type using 'declareRecord', and possibly declares
-- other functions using the other code generation functions.

{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module Common.THRecord
       (RecordDef,
        -- * Creating record data type specifications
        recordDef, uniformRecord, uniformStrictRecord, uniformNonStrictRecord,
        
        -- * Code generation
        declareRecord,
        declareFieldReaders,
        declareFieldWriters,
        initializeRecord,
        initializeRecordM,
        fieldReader,
        fieldWriter,
        fieldUpdater
        )
where

import Control.Monad
import Data.List
import Language.Haskell.TH

-- | A specification of a record data type with one constructor and many
-- fields
data RecordDef =
  RecordDef
  { recordName :: Name
  , recordFields :: RecordFields
  }

type RecordField = (String, Strict, TypeQ)
type RecordFields = [RecordField]

findByName :: String -> RecordDef -> Maybe RecordField
findByName nm rd =
  find (\(record_nm, _, _) -> nm == record_nm) $ recordFields rd

-- | Create a record data type definition
recordDef :: String -> [(String, Strict, TypeQ)] -> RecordDef
recordDef nm fields = RecordDef (mkName nm) fields

-- | Create a record data type definition where all fields have the same type
uniformRecord :: String -> [String] -> Strict -> TypeQ -> RecordDef
uniformRecord name field_names strict field_type =
  RecordDef
  { recordName = mkName name
  , recordFields = [(fname, strict, field_type)
                   | fname <- field_names]
  }

-- | Create a record data type definition where all fields are strict and
-- have the same type
uniformStrictRecord :: String -> [String] -> TypeQ -> RecordDef
uniformStrictRecord name field_names field_type =
  uniformRecord name field_names IsStrict field_type

-- | Create a record data type definition where all fields are nonstrict and
-- have the same type
uniformNonStrictRecord :: String -> [String] -> TypeQ -> RecordDef
uniformNonStrictRecord name field_names field_type =
  uniformRecord name field_names NotStrict field_type

-------------------------------------------------------------------------------

simpleFunD :: Name -> [PatQ] -> ExpQ -> DecQ
simpleFunD name params body = do
  funD name [clause params (normalB body) []]

recordType :: RecordDef -> TypeQ
recordType rd = conT $ recordName rd

fieldType :: RecordField -> TypeQ
fieldType (_, _, tyQ) = tyQ

-- | Create a data type declaration for a record type
declareRecord :: RecordDef -> DecQ
declareRecord rd = do
  dataD (cxt []) (recordName rd) [] [constructor] []
  where
    constructor =
      recC (recordName rd) [varStrictType (mkName fname) (strictType (return str) tyq)
                           | (fname, str, tyq) <- recordFields rd]

-- | Create a field reader function for each record field.
-- A reader's name consists of a field name plus a prefix.
declareFieldReaders :: RecordDef -> String -> Q [Dec]
declareFieldReaders rd prefix =
  liftM concat $ mapM declareFieldReader $ recordFields rd
  where
    declareFieldReader (fname, _, ftypeQ) = do
      param <- newName "rec"
      let fun_name = mkName $ prefix ++ fname
      
      -- Function type signature
      sig <- sigD fun_name $ arrowT `appT` recordType rd `appT` ftypeQ
      
      -- Function declaration
      fun <- simpleFunD fun_name [varP param] 
        (appE (varE $ mkName fname) (varE param))
             
      return [sig, fun]

-- | Create a field writer function for each record field.
-- A writer's name consists of a field name plus a prefix.
declareFieldWriters :: RecordDef -> String -> Q [Dec]
declareFieldWriters rd prefix =
  liftM concat $ mapM declareFieldReader $ recordFields rd
  where
    declareFieldReader (fname, _, ftypeQ) = do
      param1 <- newName "rec"
      param2 <- newName "val"
      let fun_name = mkName (prefix ++ fname)
      
      -- Function type signature
      sig <- sigD fun_name $ arrowT `appT` recordType rd `appT` (arrowT `appT` ftypeQ `appT` recordType rd)
      
      -- Function declaration
      fun <- simpleFunD fun_name [varP param1, varP param2] 
        (recUpdE (varE param1) [fieldExp (mkName fname) (varE param2)])

      return [sig, fun]

-- | An expression that creates a new record with the given initializers:
--
-- @
--   RecordType {field1 = exp1, field2 = exp2, ...}
-- @
initializeRecord :: RecordDef -> [(String, ExpQ)] -> ExpQ
initializeRecord rd fields =
  recConE (recordName rd)
  [do exp <- expQ
      return (mkName fname, exp)
  | (fname, expQ) <- fields]

-- | An expression that runs the given initializer actions in a monad and
-- uses them to create a new record:
--
-- @
--   do tmp1 <- exp1
--      tmp2 <- exp2
--      ...
--      return (RecordType {field1 = tmp1, field2 = tmp2, ...})
-- @
initializeRecordM :: RecordDef -> [(String, ExpQ)] -> ExpQ
initializeRecordM rd fields = do
  let num_fields = length fields

  -- Create a temporary variable for each value
  tmp_vars <- replicateM num_fields $ newName "val"
  
  -- Assign fields
  let field_assignments = zipWith bind_tmp_vars fields tmp_vars

  -- Create a record update expression
  rec_var <- newName "record"
  doE (field_assignments ++ [update_record fields tmp_vars])
  where
    -- Run an expression and bind it to a temporary variable
    bind_tmp_vars (_, expQ) tmp_var = bindS (varP tmp_var) expQ

    -- Update the record
    update_record fields tmp_vars =
      noBindS $
      appE [| return |] $
      recConE (recordName rd) $
      zipWith assign_name_exp fields tmp_vars
    
    assign_name_exp (name, _) tmp_var = return (mkName name, VarE tmp_var)

-- | A function that reads the specified field:
--
-- @
--   \ record -> field_name record
-- @
fieldReader :: RecordDef -> String -> ExpQ
fieldReader rd fname =
  case findByName fname rd
  of Just (name, _, _) ->
       [| \record -> $(varE $ mkName name) record |]
     Nothing -> fail "No such field"

-- | A function that writes the specified field:
--
-- @
--   \ record new_field_value -> record {field_name = new_field_value}
-- @
fieldWriter :: RecordDef -> String -> ExpQ
fieldWriter rd fname =
  case findByName fname rd
  of Just field@(name, _, _) ->
       [| \record value ->
             $(recUpdE [| record |] [fieldExp (mkName name) [| value |]]) |]
     Nothing -> fail "No such field"

-- | A function that updates the specified field:
--
-- @
--   \ record updater -> record {field_name = updater (field_name record)}
-- @
fieldUpdater :: RecordDef -> String -> ExpQ
fieldUpdater rd fname =
  case findByName fname rd
  of Just field@(name, _, _) ->
       let nm = mkName name
       in [| \record updater ->
             $(recUpdE [| record |]
               [fieldExp nm [| updater ($(varE nm) record) |]]) |]
