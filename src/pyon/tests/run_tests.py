
import os
import os.path
import sys
import traceback

import pyon.parser
from pyon.data_dir import *
import pyon.ssa.parser_ssa as ssa
import pyon.functional_conversion as functional_conversion
import untyped

# Find path to source files
testDir = os.path.join(DATA_DIR, 'testcases')

# Try to compile a test program
def tryCompile(fname, show_traceback = False):
    try:
        # Run everything up to and including ANF conversion
        test_ast = pyon.parser.parse(fname)
        ssa.convertSSA(test_ast)

        # Export the module
        test_untyped = functional_conversion.convertModule(test_ast)
        del test_ast

        # Type inference
        untyped.printModule(test_untyped) 
        test_inf = untyped.typeInferModule(test_untyped)
        del test_untyped

        # System F optimizations
        test_inf = untyped.partialEvaluateModule(test_inf)
        test_inf = untyped.eliminateDeadCode(test_inf)
        test_inf = untyped.eliminatePatternMatching(test_inf)
	print
	print "System F"
        untyped.printModule(test_inf)
        untyped.typeCheckModule(test_inf)
        test_inf = untyped.specialize(test_inf)
	print
	print "Specialized"
        untyped.printModule(test_inf)
        untyped.typeCheckModule(test_inf)
        flat = untyped.flattenModule(test_inf)

	low_level = untyped.lower(flat)
	print "Low-level"
	untyped.printModule(low_level)

        # test_sf = type_inference.inferTypes(test_anf)

        #flat_sf = untyped.flattenModule(test_inf)
	#print
	#print "Flattened to ANF"
	#untyped.printModule(flat_sf)

        #untyped.typeCheckAnfModule(flat_sf)
	# test_sf = system_f.optimizeModule(test_sf)
        # test_flat = system_f.flattenModule(test_sf)

        # (DEBUG) print the output
        # system_f.printCoreModule(test_flat)
	# system_f.typeCheckCoreModule(test_flat)
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
