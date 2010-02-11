
import os
import os.path
import sys
import traceback

import pyon.parser
import pyon.ast.print_ast as print_ast
from pyon.data_dir import *
import pyon.ssa.parser_ssa as ssa
import pyon.anf_conversion as anf_conversion
import pyon.type_inference as type_inference
import pyon.partial_eval as partial_eval

# Find path to source files
testDir = os.path.join(DATA_DIR, 'testcases')

# Try to compile a test program
def tryCompile(fname, show_traceback = False):
    try:
        # Run everything up to and including ANF conversion
        test_ast = pyon.parser.parse(fname)
        ssa.convertSSA(test_ast)
        test_anf = anf_conversion.convertModule(test_ast)

        # Type inference
        test_anf = type_inference.inferTypes(test_anf)

        # Partial evaluation
        #test_anf = partial_eval.partialEval(test_anf)
        #test_anf = partial_eval.eliminateDeadCode(test_anf)
        
        # (DEBUG) print the output with type?
        # print_system_f.renderAst(test_anf)

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
