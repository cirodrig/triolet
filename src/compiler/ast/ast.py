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

    def __init__(self, name):
        self.name = name
        

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

# The default value of ExprInit
ExprInit.default = ExprInit() 

class Expr(object):
    """An abstract base class of expressions."""

    def __init__(self, arg):
        arg.initializeExpr(self)

class VariableExpr(Expr):
    """A reference to a variable"""
    
    def __init__(self, v, base = ExprInit.default):
        Expr.__init__(self, base)
        self.variable = v

class LiteralExpr(Expr):
    """A reference to a primitive, immutable literal value.

    Literals can be numbers, booleans, or the None value."""

    def __init__(self, l, base = ExprInit.default):
        Expr.__init__(self, base)
        self.literal = l

class UnaryExpr(Expr):
    """An application of a unary operator to an operand."""

    def __init__(self, op, arg, base = ExprInit.default):
        Expr.__init__(self, base)
        assert isinstance(op, operators.UnaryOp)
        assert isinstance(arg, Expr)
        self.operator = op
        self.argument = arg

class BinaryExpr(Expr):
    """An application of a binary operator to left and right operands."""

    def __init__(self, op, left, right, base = ExprInit.default):
        Expr.__init__(self, base)
        assert isinstance(op, operators.BinaryOp)
        assert isinstance(left, Expr)
        assert isinstance(right, Expr)
        self.operator = op
        self.left = left
        self.right = right

class LetExpr(Expr):
    """An assignment expression"""
    def __init__(self, name, rhs, body, base = ExprInit.default):
        Expr.__init__(self, base)
        assert isinstance(name, Variable)
        assert isinstance(rhs, Expr)
        assert isinstance(body, Expr)
        self.name = name
        self.rhs = rhs
        self.body = body

class LetrecExpr(Expr):
    """A set of function definitions"""
    def __init__(self, definitions, body, base = ExprInit.default):
        Expr.__init__(self, base)
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
