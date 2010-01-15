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

    # A counter used to assign unique IDs to variables
    _nextID = 1

    @classmethod
    def getNewID(cls):
        """
        Get a new, globally unique ID that can be used to initialize
        an ANFVariable.
        """
        id = cls._nextID
        cls._nextID = id + 1
        return id

class ANFVariable(Variable):
    """
    A single-assignment variable used in ANF.  Only one instance of this
    object exists for each variable.

    Variables can carry type information, which may be a first-order
    type or a type scheme.  Type information is inserted when the
    variable is created or during type inference.

    Fields:
    name:
      The variable's name as it appears in source code.
    identifier:
      An integer that uniquely identifies this variable.
    """

    def __init__(self, name = None, identifier = None, type_scheme = None):
        """
        Create a new variable.  The variable should have a globally
        unique ID.

        Optional parameters:
        name:
          The variable's name as it appears in source code
        identifier:
          An integer that uniquely identifies this variable
          (If not given, a new integer will be assigned to the variable)
        type_scheme:
          The variable's type; if None, the type should be inferred
        """
        assert name is None or isinstance(name, str)

        # If no identifier is given, create a new variable
        if identifier is None:
            identifier = Variable.getNewID()
        else:
            assert isinstance(identifier, int)
        self.name = name
        self.identifier = identifier
        self._typeScheme = type_scheme

    def __eq__(self, other):
        return self.identifier == other.identifier

    def setTypeScheme(self, type_scheme):
        # Cannot change a variable's type
        if self._typeScheme:
            raise RuntimeError, "Attempted to re-assign a variable's type"

        self._typeScheme = type_scheme

    def getTypeScheme(self):
        """
        Return this variable's type scheme, or None if it does not have a
        type scheme.
        """
        return self._typeScheme

    def getType(self):
        """
        Create the type of an instance of this variable.  Returns a type.
        The variable must have been assigned a type.
        """
        return self._typeScheme.instantiate()

    _nextID = 0

    @classmethod
    def getNewID(cls):
        "Get a new, globally unique identifier"
        n = ANFVariable._nextID
        ANFVariable._nextID = n + 1
        return n

class InstanceVariable(Variable):
    """A class dictionary variable."""

    def __init__(self):
        raise NotImplementedError

###############################################################################
# Parameters

class Parameter(object):
    """
    A parameter of a function or destination of an assignment.

    Fields created by type inference:
      type: HM type
    """

    def __init__(self):
        self.type = None        # Assigned by type inference

class VariableParam(Parameter):
    """
    A variable parameter.
    """

    def __init__(self, v, annotation = None, default = None):
        assert isinstance(v, Variable)
        Parameter.__init__(self)
        self.name = v
        self.annotation = annotation
        self.default = default

class TupleParam(Parameter):
    """
    A tuple parameter.
    """

    def __init__(self, fields):
        for p in fields:
            assert isinstance(p, Parameter)
        Parameter.__init__(self)
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
        expr.type = None        # Assigned by type inference
        return None

# The default value of ExprInit
ExprInit.default = ExprInit() 

class Expression(object):
    """
    An abstract base class of expressions.

    Fields created by type inference:
      type: HM type
    """

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

class UndefinedExpr(Expression):
    """An undefined value of any type."""

    def __init__(self, base = ExprInit.default):
        base.initializeExpr(self)

class TupleExpr(Expression):
    """A tuple expression."""

    def __init__(self, arguments, base = ExprInit.default):
        base.initializeExpr(self)
        for f in arguments:
            assert isinstance(f, Expression)
        self.arguments = arguments

class CallExpr(Expression):
    """A function call."""

    def __init__(self, operator, arguments, base = ExprInit.default):
        base.initializeExpr(self)
        assert isinstance(operator, Expression)
        for arg in arguments:
            assert isinstance(arg, Expression)
        self.operator = operator
        self.arguments = arguments
        self.cstArguments = None # Assigned by type inference

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
        self.parameter = lhs
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

    # A function runs either as an ordinary expression or as an iterator.
    # All user-defined functions are EXPRESSION functions.  Generator
    # expressions and some built-in functions are ITERATOR functions.
    EXPRESSION = 1
    ITERATOR = 2

    def __init__(self, mode, parameters, body):
        assert mode == Function.EXPRESSION or mode == Function.ITERATOR
        for p in parameters:
            assert isinstance(p, Parameter)
        assert isinstance(body, Expression)
        self.mode = mode
        self.qvars = None       # Assigned by type inference
        self.parameters = parameters
        self.instanceParameters = None # Assigned by type inference
        self.body = body

def exprFunction(parameters, body):
    "Create an expression function"
    return Function(Function.EXPRESSION, parameters, body)

def iterFunction(parameters, body):
    "Create an iterator function"
    return Function(Function.ITERATOR, parameters, body)

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
