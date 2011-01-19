
module CParser2.Driver(parseCoreModule)
where

import System.FilePath
import System.IO

import Gluon.Common.Error
import Gluon.Common.SourcePos
import Gluon.Common.Identifier
import Builtins.Builtins
import Type.Var
import Type.Type
import Type.Environment
import CParser2.AST
import CParser2.Lexer
import CParser2.Parser
import CParser2.Resolve
import CParser2.LevelInference
import CParser2.GenCore
import LowLevel.Label
import Paths

import CParser2.PrettyAST()

predefinedVarDetails :: [(String, VarDetails)]
predefinedVarDetails = map mk_var_details (pureV : allBuiltinVars)
  where
    mk_var_details v = (name, PredefinedVar v)
      where
        name =
          case varName v
          of Just lab -> case labelLocalName lab
                         of Left name -> name
                            _ -> internalError "Unnamed predefined variable"
             _ -> internalError "Unnamed predefined variable"
  {-
  [(varNameString $ Gluon.varName v, PredefinedVar v) | v <- vars] ++
  [(labelUnqualifiedName $ Gluon.conName c, PredefinedCon c) | c <- cons] ++
  [ ("Pure", PredefinedKind Gluon.PureKind)
  , ("Effect", PredefinedKind Gluon.EffectKind)
  ]
  where
    varNameString (Just l) = labelUnqualifiedName l
    varNameString Nothing = internalError "parseCoreModule: Variable has no name"
    vars = [ pyonBuiltin the_passConv_int_addr
           , pyonBuiltin the_passConv_float_addr
           , pyonBuiltin the_eqDict_int_addr
           , pyonBuiltin the_eqDict_float_addr
           , pyonBuiltin the_additiveDict_int_zero_addr
           , pyonBuiltin the_additiveDict_float_zero_addr
           , pyonBuiltin the_multiplicativeDict_int_one_addr
           , pyonBuiltin the_multiplicativeDict_float_one_addr
           , pyonBuiltin the_OpaqueTraversableDict_list_addr
           ]
    cons = [ -- Data types
             pyonBuiltin the_PassConv
           , pyonBuiltin the_int
           , pyonBuiltin the_float
           , pyonBuiltin the_bool
           , pyonBuiltin the_NoneType
           , pyonBuiltin the_complex
           , pyonBuiltin the_list
           , pyonBuiltin the_LazyStream
           , getPyonTupleType' 2
           , getPyonTupleCon' 2
           , Gluon.builtin Gluon.the_EmpE
           , Gluon.builtin Gluon.the_AtE
           , Gluon.builtin Gluon.the_SconjE
             
             -- Data constructors
           , pyonBuiltin the_makeComplex
             
             -- Load/store functions
           , pyonBuiltin the_fun_load_int
           , pyonBuiltin the_fun_load_float
           , pyonBuiltin the_fun_load_bool
           , pyonBuiltin the_fun_load_NoneType
           , pyonBuiltin the_fun_load_complexFloat
           , pyonBuiltin the_fun_store_int
           , pyonBuiltin the_fun_store_float
           , pyonBuiltin the_fun_store_bool
           , pyonBuiltin the_fun_store_NoneType
           , pyonBuiltin the_fun_store_complexFloat

             -- Representation dictionaries
           , pyonBuiltin the_passConv_int
           , pyonBuiltin the_passConv_float
           , pyonBuiltin the_passConv_owned
           , pyonBuiltin the_passConv_iter
           , pyonBuiltin the_passConv_list
           , getPyonTuplePassConv' 2
             
             -- Comparison dictionaries
           , pyonBuiltin the_EqDict
           , pyonBuiltin the_eqDict
           
           , pyonBuiltin (eqMember . the_EqDict_int)
           , pyonBuiltin (neMember . the_EqDict_int)
           
           , pyonBuiltin (eqMember . the_EqDict_float)
           , pyonBuiltin (neMember . the_EqDict_float)
             
           , pyonBuiltin the_eqDict_Tuple2
           , pyonBuiltin (eqMember . the_EqDict_Tuple2)
           , pyonBuiltin (neMember . the_EqDict_Tuple2)

           , pyonBuiltin the_OrdDict
           , pyonBuiltin the_ordDict
           
           , pyonBuiltin the_ordDict_Tuple2
           , pyonBuiltin (ltMember . the_OrdDict_int)
           , pyonBuiltin (leMember . the_OrdDict_int)
           , pyonBuiltin (gtMember . the_OrdDict_int)
           , pyonBuiltin (geMember . the_OrdDict_int)
           
           , pyonBuiltin (ltMember . the_OrdDict_float)
           , pyonBuiltin (leMember . the_OrdDict_float)
           , pyonBuiltin (gtMember . the_OrdDict_float)
           , pyonBuiltin (geMember . the_OrdDict_float)

           , pyonBuiltin (ltMember . the_OrdDict_Tuple2)
           , pyonBuiltin (leMember . the_OrdDict_Tuple2)
           , pyonBuiltin (gtMember . the_OrdDict_Tuple2)
           , pyonBuiltin (geMember . the_OrdDict_Tuple2)

             -- Numeric dictionaries
           , pyonBuiltin the_AdditiveDict
           , pyonBuiltin the_additiveDict
           
           , pyonBuiltin (zeroMember . the_AdditiveDict_int)
           , pyonBuiltin (addMember . the_AdditiveDict_int)
           , pyonBuiltin (subMember . the_AdditiveDict_int)
           , pyonBuiltin (negateMember . the_AdditiveDict_int)
             
           , pyonBuiltin (zeroMember . the_AdditiveDict_float)
           , pyonBuiltin (addMember . the_AdditiveDict_float)
           , pyonBuiltin (subMember . the_AdditiveDict_float)
           , pyonBuiltin (negateMember . the_AdditiveDict_float)
             
           , pyonBuiltin the_additiveDict_complex
             
           , pyonBuiltin the_MultiplicativeDict
           , pyonBuiltin the_multiplicativeDict
             
           , pyonBuiltin (mulMember . the_MultiplicativeDict_int)
           , pyonBuiltin (fromIntMember . the_MultiplicativeDict_int)
           , pyonBuiltin (oneMember . the_MultiplicativeDict_int)

           , pyonBuiltin (mulMember . the_MultiplicativeDict_float)
           , pyonBuiltin (fromIntMember . the_MultiplicativeDict_float)
           , pyonBuiltin (oneMember . the_MultiplicativeDict_float)

             -- Traversable dictionaries
           , pyonBuiltin the_TraversableDict
           , pyonBuiltin the_traversableDict
             
           , pyonBuiltin (traverseMember . the_TraversableDict_list)
           , pyonBuiltin (buildMember . the_TraversableDict_list)

           , pyonBuiltin (traverseMember . the_TraversableDict_Stream)
           , pyonBuiltin (buildMember . the_TraversableDict_Stream)

           , pyonBuiltin the_OpaqueTraversableDict_list
             
             -- Other functions
           , pyonBuiltin the_fun_copy
           , pyonBuiltin the_oper_CAT_MAP
           , pyonBuiltin the_fun_map_Stream
           , pyonBuiltin the_fun_reduce
           , pyonBuiltin the_fun_reduce_Stream
           , pyonBuiltin the_fun_return
           , pyonBuiltin the_fun_generate
           , pyonBuiltin the_fun_generateList
           , pyonBuiltin the_fun_vectorGenerateList
           ]-}

parseCoreModule :: IdentSupply Var -> IO TypeEnv
parseCoreModule ident_supply = do
  pathname <- getDataFileName ("symbols" </> "coretypes2")
  input_file <- readFile pathname
  
  -- Parse file
  let input_tokens = lexify pathname input_file
  parsed_ast <- parseFile pathname input_tokens

  -- Resolve names
  let modname = moduleName $ takeBaseName pathname
  resolve_env <- globalEnvironment ident_supply predefinedVarDetails
  resolved_ast <- resolveModule ident_supply resolve_env modname parsed_ast
  
  -- Compute levels
  level_ast <- levelInferModule resolved_ast

  -- Convert to core expressions
  return $ createCoreTable level_ast
