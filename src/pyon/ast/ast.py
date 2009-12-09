# ast.py
#
# The main AST data structures are defined here

import itertools

# Operator names
import pyon.ast.operators

class Variable(object):
    """Abstract base class of variables"""

    def __init__(self):
        raise NotImplementedError, "'Variable' is an abstract base class"

    def __eq__(self, other):
        raise NotImplementedError, "'Variable' is an abstract base class"

class ANFVariable(Variable):
    """A single-assignment variable used in ANF."""

    def __init__(self, name, identifier):
        """ANFVariable(string-or-None, int) -> new variable
        Create a new variable.  The variable should have a globally
        unique ID."""
        # Variables have an optional name 
        assert isinstance(name, str) or name is None
        assert isinstance(identifier, int)
        self.name = name
        self.identifier = identifier

    def __eq__(self, other):
        return self.identifier == other.identifier

###############################################################################
# Parameters

class Parameter(object):
    """A function parameter"""

    def __init__(self):
        raise NotImplementedError, "'Parameter' is an abstract base class"

class VariableParam(Parameter):
    """A variable function parameter"""

    def __init__(self, v, annotation = None, default = None):
        assert isinstance(v, Variable)
        self.name = v
        self.annotation = annotation
        self.default = default

class TupleParam(Parameter):
    """A tuple parameter"""

    def __init__(self, fields):
        for p in fields:
            assert isinstance(p, Parameter)
        self.fields = fields

###############################################################################
# Expressions

class ExprInit(object):
    """An initializer for expression base types"""

    def __init__(self):
        """Initialize this expression."""
        pass

    def initializeExpr(self, expr):
        """Initialize an 'Expression'.
        This is called from the expression's __init__ method."""
        return ()

# The default value of ExprInit
ExprInit.default = ExprInit() 

class Expression(object):
    """An abstract base class of expressions."""

    def __init__(self, arg):
        raise NotImplementedError, "'Expression' is an abstract base class"

## These expressions are generated from Python expressions (not statements)

class VariableExpr(Expression):
    """A reference to a variable"""

    def __init__(self, v, base = ExprInit.default):
        base.initializeExpr(self)
        self.variable = v

class LiteralExpr(Expression):
    """A reference to a primitive, immutable literal value.

    Literals can be numbers, booleans, or the None value."""

    def __init__(self, l, base = ExprInit.default):
        base.initializeExpr(self)
        self.literal = l

class UnaryExpr(Expression):
    """An application of a unary operator to an operand."""

    def __init__(self, op, arg, base = ExprInit.default):
        base.initializeExpr(self)
        assert isinstance(op, operators.UnaryOp)
        assert isinstance(arg, Expression)
        self.operator = op
        self.argument = arg

class BinaryExpr(Expression):
    """An application of a binary operator to left and right operands."""

    def __init__(self, op, left, right, base = ExprInit.default):
        base.initializeExpr(self)
        assert isinstance(op, operators.BinaryOp)
        assert isinstance(left, Expression)
        assert isinstance(right, Expression)
        self.operator = op
        self.left = left
        self.right = right

class StreamExpr(Expression):
    """A stream expression."""

    def __init__(self, iterator, base = ExprInit.default):
        base.initializeExpr(self)
        assert isinstance(iterator, Iterator)
        self.iterator = iterator

class CallExpr(Expression):
    """A function call."""

    def __init__(self, operator, arguments, base = ExprInit.default):
        base.initializeExpr(self)
        assert isinstance(operator, Expression)
        for arg in arguments:
            assert isinstance(arg, Expression)
        self.operator = operator
        self.arguments = arguments

## These expressions can be generated from either Python expressions
## or Python statements

class IfExpr(Expression):
    """An if-else expression."""

    def __init__(self, argument, ifTrue, ifFalse, base = ExprInit.default):
        base.initializeExpr(self)
        assert isinstance(argument, Expression)
        assert isinstance(ifTrue, Expression)
        assert isinstance(ifFalse, Expression)
        self.argument = argument
        self.ifTrue = ifTrue
        self.ifFalse = ifFalse

class FunExpr(Expression):
    """A lambda function"""
    def __init__(self, function, base = ExprInit.default):
        base.initializeExpr(self)
        assert isinstance(function, Function)
        self.function = function

## These expressions are generated from Python statements

class LetExpr(Expression):
    """An assignment expression"""
    def __init__(self, lhs, rhs, body, base = ExprInit.default):
        base.initializeExpr(self)
        assert lhs is None or isinstance(lhs, Parameter)
        assert isinstance(rhs, Expression)
        assert isinstance(body, Expression)
        self.name = lhs
        self.rhs = rhs
        self.body = body

class LetrecExpr(Expression):
    """A set of function definitions"""
    def __init__(self, definitions, body, base = ExprInit.default):
        base.initializeExpr(self)
        for d in definitions: assert isinstance(d, FunctionDef)
        assert isinstance(body, Expression)
        self.definitions = definitions
        self.body = body

###############################################################################
# Generators

class IterInit(object):
    def __init__(self):
        pass

    def initializeIter(self, iter):
        """Initialize an 'Iterator'.
        This is called from the iterator's __init__ method."""
        pass

IterInit.default = IterInit()

class Iterator(object):
    """A stream expression."""
    def __init__(self):
        raise NotImplementedError, "'Iterator' is an abstract base class"

class ForIter(Iterator):
    """A stream that traverses an object."""
    
    def __init__(self, param, argument, body, base = IterInit.default):
        base.initializeIter(self)
        assert isinstance(param, Parameter)
        assert isinstance(argument, Expression)
        assert isinstance(body, Iterator)
        self.parameter = param
        self.argument = argument
        self.body = body

class IfIter(Iterator):
    """A stream that traverses a subset of an iteration space."""

    def __init__(self, guard, body, base = IterInit.default):
        base.initializeIter(self)
        assert isinstance(guard, Expression)
        assert isinstance(body, Iterator)
        self.guard = guard
        self.body = body

class DoIter(Iterator):
    """A stream that produces a single value."""

    def __init__(self, body, base = IterInit.default):
        base.initializeIter(self)
        assert isinstance(body, Expression)
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
    def __init__(self, parameters, body, local_scope = None):
        for p in parameters:
            assert isinstance(p, Parameter)
        assert isinstance(body, Expression)
        self.parameters = parameters
        self.body = body
        self.localScope = local_scope

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
