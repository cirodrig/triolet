
import haskell
import untyped
import pyon.types.hmtype
import pyon.types.kind as kind
import pyon.ast.parser_ast as ast
# from pyon.builtin_data import BUILTIN_FUNCTIONS, BUILTIN_DATATYPES

# A list of PythonVariable used for resolving the names of predefined
# variables while parsing.
_builtinVariableList = None

# def _getBuiltinVariableList():
#     global _builtinVariableList

#     # Initialize the list if needed, do nothing otherwise
#     if _builtinVariableList is None:
#         def mv(anf_var):
#             "Create the list entry for @anf_var."

#             # Don't use the ID of the ANF variable id; have the constructor
#             # create a new ID.
#             return ast.PythonVariable(anf_var.name, anf_variable = anf_var)

#         def mv2(con):
#             "Create the list entry for the data type constructor @con."
#             return ast.PythonVariable(con.name,
#                                       anf_type = pyon.types.hmtype.EntTy(con))

#         functions = [mv(v) for v in BUILTIN_FUNCTIONS]
#         types = [mv2(con) for con in BUILTIN_DATATYPES]

#         kinds = [ast.PythonVariable("type", anf_kind = kind.Star())]

#         _builtinVariableList = functions + types + kinds

#     return _builtinVariableList

def _getBuiltinVariableList():
    global _builtinVariableList

    # Initialize the list if needed
    if _builtinVariableList is None:
        def mv(name, obj):
            return ast.PythonVariable(name, anf_variable = obj)

        def mt(name, ty):
            return ast.PythonVariable(name, anf_type = ty)

        functions = [mv(name, obj) for name, obj in untyped.GLOBAL_VARIABLES]
        types = [mt(name, ty) for name, ty in untyped.BUILTIN_TYPES]
        kinds = [ast.PythonVariable("type", anf_kind = untyped.Star)]
        _builtinVariableList = functions + types + kinds

    return _builtinVariableList

def parse(fname):
    """
    parse(filename) -> pyon-module
    Parse a file.  Throws an exception if a parse error occurs.

    The parser updates the counter used to generate variable IDs.
    The global variables defined in builtin_data.py are assigned IDs the
    first time parse() is called.
    """
    # Create a (name, ID, variable) lookup table for the parser
    var_list = [(v.name, v.identifier, v) for v in _getBuiltinVariableList()]

    # Get the ID generator
    id_gen = ast.PythonVariable.getIDGenerator()

    # Run the parser
    (id_gen, module) = haskell.parse(fname, var_list, id_gen)

    # Save the new ID generator
    ast.PythonVariable.setIDGenerator(id_gen)

    return module
