
import os
import os.path
import sys
import traceback

import haskell
import pyon.ast.parser_ast as parser_ast
import pyon.ast.print_ast as print_ast
from pyon.data_dir import *
import pyon.ssa.parser_ssa as ssa
import pyon.anf_conversion as anf_conversion

import pyon.type_inference as type_inference

# Find path to source files
testDir = os.path.join(DATA_DIR, 'testcases')

# Try to compile a test program
def tryCompile(fname, show_traceback = False):
    try:
        # Run everything up to and including ANF conversion
        (variable_id, test_ast) = haskell.parse(fname)
        parser_ast.PythonVariable.setIDGenerator(variable_id) 
        ssa.convertSSA(test_ast)
        test_anf = anf_conversion.convertModule(test_ast)

        # (DEBUG) print the output
        print_ast.printAst(test_anf)

        # Type inference
        type_inference.inferTypes(test_anf)

        # print the output with type?
        print_ast.printAst(test_anf)

    except Exception, e:
        print e
        if show_traceback:
            print "Traceback:"
            traceback.print_tb(sys.exc_traceback) # Print stack trace
            print
        print "Test failed:", fname
        return False

    return True

###############################################################################
# Main code

def main(show_traceback = False):
    pass_count = fail_count = count = 0
    
    # For each test file
    print "Starting Tests..."
    for dir, subdirs, files in os.walk(testDir):
        files.sort()
        for f in files:
            # Run test
            path = os.path.join(dir, f)
            print "Testing %s..." % path
            succ = tryCompile(path, show_traceback=True)

            # Update statistics
            count = count + 1
            if succ:
                pass_count = pass_count + 1
            else:
                fail_count = fail_count + 1

    print pass_count, "of", count, "tests passed"
