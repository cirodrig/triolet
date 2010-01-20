
import haskell
import pyon.ast.parser_ast as ast
from pyon.builtin_data import BUILTIN_FUNCTIONS

# A list of PythonVariable used for resolving the names of predefined
# variables while parsing.
_builtinVariableList = None

def _getBuiltinVariableList():
    global _builtinVariableList

    # Initialize the list if needed, do nothing
    if _builtinVariableList is None:
        def mv(anf_var):
            "Create the list entry for @anf_var."

            # Don't use the ID of the ANF variable id; have the constructor
            # create a new ID.
            return ast.PythonVariable(anf_var.name, anf_variable = anf_var)

        _builtinVariableList = [mv(v) for v in BUILTIN_FUNCTIONS]

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
