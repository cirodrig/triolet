
import ast
import haskell
#import ssa
#import type_inference
#import optimizations
#import cbv

def compile(filename):
    # Parse
    parse_tree = haskell.parse(filename)

    # SSA and control conversion
    #anf_form = ssa.convertToANF(parse_tree)
    #del parse_tree

    # Type inference
    #type_inference.inferTypes(anf_form)

    # High-level optimizations to remove abstraction
    #optimizations.inlineGlobally(anf_form)
    #optimizations.specializeGlobally(anf_form)

    # Call-by-value conversion
    #gluon_form = cbv.convertToGluon(anf_form)
    #del anf_form

    # Do the rest of the compilation and produce output
    #haskell.compileGluon(gluon_form)

import sys

compile(sys.argv[1])
