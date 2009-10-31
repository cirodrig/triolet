# This Python module runs the Pyon parser.
# The parser is a separate program.  It is called as a subprocess.
# Its output is Python code that is evaluated to produce the AST.

import subprocess
import ast

# The program that performs parsing 
_PARSER = "pyon_parser"

def _makeDictionary():
    """Create the global environemnt in which the parser data structures
    will be built."""
    env = dict(ast.__dict__)

    # Maintain a lookup table of variables.  Variables are found by ID
    # in this table.
    var_table = dict()

    def makeVariable(name, id):
        try:
            v = var_table[id]
        except KeyError:
            v = ast.PythonVariable(name, id)
            var_table[id] = v

        return v

    env['makeVariable'] = makeVariable

    return env

def run(filename):
    """Parse a file and return the generated AST."""
    process = subprocess.Popen([_PARSER, filename],
                               stdout=subprocess.PIPE)
    command, _ = process.communicate()

    # Evaluate the output to build the AST
    data = eval(command, _makeDictionary())

    return data
