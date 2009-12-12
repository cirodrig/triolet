
import os
import os.path

import haskell
import pyon.ast
from pyon.data_dir import *

# Find path to source files
testDir = os.path.join(DATA_DIR, 'testcases')

# Try to compile a test program
def tryCompile(fname):
    try:
        # Currently we only run the parser
        haskell.parse(fname)
    except Exception, e:
        print e
        print "Test failed:", fname
        return False

    return True

###############################################################################
# Main code

def main():
    pass_count = fail_count = count = 0
    
    # For each test file
    print "Starting tests..."
    for dir, subdirs, files in os.walk(testDir):
        for f in files:
            # Run test
            path = os.path.join(dir, f)
            succ = tryCompile(path)

            # Update statistics
            count = count + 1
            if succ:
                pass_count = pass_count + 1
            else:
                fail_count = fail_count + 1

    print pass_count, "of", count, "tests passed"
