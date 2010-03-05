
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
import system_f

# Find path to source files
testDir = os.path.join(DATA_DIR, 'testcases')

# Try to compile a test program
def tryCompile(fname, show_traceback = False):
    try:
        # Run everything up to and including ANF conversion
        test_ast = pyon.parser.parse(fname)
        ssa.convertSSA(test_ast)
        test_anf = anf_conversion.convertModule(test_ast)
	del test_ast

        # Type inference
        test_sf = type_inference.inferTypes(test_anf)
	del test_anf

        system_f.typeCheckModule(test_sf)
	test_sf = system_f.optimizeModule(test_sf)
        test_flat = system_f.flattenModule(test_sf)

        # (DEBUG) print the output
	system_f.printCoreModule(test_flat)
	system_f.typeCheckCoreModule(test_flat)
        # test_flat = system_f.effectInferCoreModule(test_flat)
	#system_f.printCoreModule(test_flat)

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
