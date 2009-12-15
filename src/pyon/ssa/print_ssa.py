"""
Pretty-print ssa-specific data structures (not ssa-annotations, though)
"""

from pyon.ssa.parser_ssa import *
import pyon.pretty as pretty
import pyon.ast.parser_ast as ast

def prettySSA(obj):
    """Pretty-print SSA data structures"""
    if isinstance(obj, IfNode):
        return pretty.space(['<JP',obj.num,obj.hasret, _prPhis(obj.phiNodes), '>'])
    elif isinstance(obj, ReturnNode):
        return pretty.space(['<JP',obj.num, _prPhis(obj.phiNodes), '>'])
    else:
        raise TypeError, type(obj)

def _tuple(items):
    return pretty.parens(
        pretty.space(
        pretty.punctuate(',', [prettyAst(i) for i in items])))

def _prPhis(phis):
    def _printPhi(var, phinode):
        vardoc = pretty.abut([var.name, phinode.ssaVersion])
        phidoc = pretty.parens(pretty.space([ver for stmt, ver in phinode.paths]))
        return pretty.space([vardoc, phidoc])
    return pretty.nest(
              pretty.stack(_printPhi(var, phis[var]) for var in phis.keys()), 5)
