# ast.py
#
# The main AST data structures are defined here

import itertools

# Operator names
import operators

class Variable(object):
    """Abstract base class of variables"""

    def __init__(self):
        raise NotImplementedError, "'Variable' is an abstract base class"

class PythonVariable(Variable):
    """A variable as determined by Python's name resolution rules"""

###############################################################################
# Expressions

class ExprInit(object):
    """An initializer for expression base types"""

    def __init__(self, astHandle = None):
        """Initialize this expression.

        astHandle: A handle to the original, printable AST data structure."""
        pass

    def initializeExpr(self, expr):
        """Initialize an 'Expression'.
        This is called from the expression's __init__ method."""
        return ()

class Expr(object):
    def __init__(self, arg):
        arg.initializeExpr(self)

class VariableExpr(Expr):
    """A reference to a variable"""
    def __init__(self, initobj, v):
        Expr.__init__(self, initobj)
        self.variable = v

class LiteralExpr(Expr):
    """A reference to a literal, non-compound value"""
    def __init__(self, initobj, l):
        Expr.__init__(self, initobj)
        self.literal = l

class LetExpr(Expr):
    """An assignment expression"""
    def __init__(self, initobj, name, rhs, body):
        Expr.__init__(self, initobj)
        assert isinstance(name, Variable)
        assert isinstance(rhs, Expr)
        assert isinstance(body, Expr)
        self.name = name
        self.rhs = rhs
        self.body = body

class LetrecExpr(Expr):
    """A set of function definitions"""
    def __init__(self, initobj, definitions, body):
        Expr.__init__(self, initobj)
        for d in definitions: assert isinstance(d, FunctionDef)
        assert isinstance(body, Expr)
        self.definitions = definitions
        self.body = body

###############################################################################
# Functions

class FunctionDef(object):
    """A named function definition"""
    def __init__(self, name, function):
        assert isinstance(name, Variable)
        assert isinstance(function, Function)
        self.name = name
        self.function = function

class Function(object):
    """A function or lambda term"""
    def __init__(self, parameters, body):
        for p in parameters:
            assert isinstance(p, Variable)
        assert isinstance(body, Expr)
        self.parameters = parameters
        self.body = body

###############################################################################
# Modules

class Module(object):
    """A module.

    The module consists of a list of definition groups.  Each definition
    group is a list of function definitions."""
    def __init__(self, definitions):
        for dg in definitions:
            for d in dg:
                assert isinstance(d, FunctionDef)
        self.definitions = definitions

    def iterDefinitionGroups(self):
        """Get an iterator over the module's definition groups"""
        return iter(self.definitions)

    def iterDefinitions(self):
        """Get an iterator over all definitions in the module"""
        return itertools.chain(*self.definitions)
