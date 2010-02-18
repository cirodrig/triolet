# ast.py
#
# The main AST data structures are defined here

import itertools

# Operator names
import pyon.ast.operators

import system_f
import pyon.types.gluon_types
import pyon.types.type_assignment

# Code executes in one of two modes, as an expression or as an iterator.
# All user-defined functions are in EXPRESSION mode.  Generator
# expressions and some built-in functions are in ITERATOR mode.
EXPRESSION = 1
ITERATOR = 2

###############################################################################
# Variables

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

    Variables can have a polymorphic type.  Variable types are stored as
    type schemes.  Type information is inserted when the
    variable is created or during type inference.

    In variables that are function names, the type variables bound in
    the variable's type scheme are the same type variables used in the
    function body.

    Fields:
    name:
      The variable's name as it appears in source code.
    identifier:
      An integer that uniquely identifies this variable.
    sfTranslation:
      The System F translation of this variable, if this variable is created
      to represent a preexisting System F object.  If the translation is to
      be determined by type inference, this field is None.
    sfVariable:
      The system F translation of this variable, created on demand.  This is
      only used if sfTranslation is None.
    """

    def __init__(self, name = None, identifier = None,
                 system_f_translation = None):
        """
        Create a new variable.  The variable should have a globally
        unique ID.

        Optional parameters:
        name:
          The variable's name as it appears in source code
        identifier:
          An integer that uniquely identifies this variable
          (If not given, a new integer will be assigned to the variable)
        system_f_translation:
          A system F translation of this variable, and HM type information.
          This parameter should be
          given iff the variable is not defined in Pyon code.  For example,
          built-in variables have a system F value.
        """
        assert name is None or isinstance(name, str)
        assert system_f_translation is None or \
            isinstance(system_f_translation, pyon.types.type_assignment.TypeAssignment)

        # If no identifier is given, create a new variable
        if identifier is None:
            identifier = Variable.getNewID()
        else:
            assert isinstance(identifier, int)

        self.name = name
        self.identifier = identifier
        self._sfTranslation = system_f_translation
        self._sfVariable = None

    def __eq__(self, other):
        return self.identifier == other.identifier

    def isPredefined(self): return bool(self._sfTranslation)

    def getSystemFVariable(self):
        if self._sfTranslation:
            raise RuntimeError, \
                "Variable translates to an expression, not a variable"

        v = self._sfVariable
        if not v: v = self._sfVariable = system_f.newVar(self.name)
        return v

    def getSystemFTranslation(self):
        """
        v.getSystemFTranslation() -> TypeAssignment or None

        Get the System F assignment of this variable, if it has one.
        """
        return self._sfTranslation

    def addAllTypeVariables(self, s):
        pass

    # A counter used to assign unique IDs to variables
    _nextID = 1

###############################################################################
# Parameters

class Parameter(object):
    """
    A parameter of a function or destination of an assignment.

    After type inference, a parameter that is not generalized by HM type
    inference has a type.  Parameters that are generalized do not have a
    type, but variables bound by them have type schemes.
    """

    def __init__(self):
        pass

class VariableParam(Parameter):
    """
    A variable parameter.

    Fields:
    name : string or None
      The variable name as it appeard in source code
    annotation : None
      Unused
    default : None
      Unused
    """

    def __init__(self, v, annotation = None, default = None):
        assert isinstance(v, Variable)
        Parameter.__init__(self)
        self.name = v
        self.annotation = annotation
        self.default = default

    def addAllTypeVariables(self, s):
        self.name.addAllTypeVariables(s)

class TupleParam(Parameter):
    """
    A tuple parameter.
    """

    def __init__(self, fields):
        for p in fields: assert isinstance(p, Parameter)
        Parameter.__init__(self)
        self.fields = fields

    def addAllTypeVariables(self, s):
        for p in self.fields: p.addAllTypeVariables(s)

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
        return

def copyTypedExpr(expr):
    """
    Copy properties of an expression for use in initializing another
    expression.
    """
    return ExprInit()

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

    def addAllTypeVariables(self, s):
        """
        Add all type variables referenced in this expression to the set.
        This is used when printing expressions.
        """
        pass

## These expressions are generated from Python expressions (not statements)

class VariableExpr(Expression):
    """A reference to a variable"""

    def __init__(self, v, base = ExprInit.default):
        base.initializeExpr(self)
        self.variable = v

    def addAllTypeVariables(self, s):
        self.variable.addAllTypeVariables(s)

class LiteralExpr(Expression):
    """A reference to a primitive, immutable literal value.

    Literals can be numbers, booleans, or the None value."""

    def __init__(self, l, base = ExprInit.default):
        base.initializeExpr(self)
        self.literal = l

    def addAllTypeVariables(self, s):
        pass

class UndefinedExpr(Expression):
    """An undefined value of any type."""

    def __init__(self, base = ExprInit.default):
        base.initializeExpr(self)

    def addAllTypeVariables(self, s):
        pass

class TupleExpr(Expression):
    """A tuple expression."""

    def __init__(self, arguments, base = ExprInit.default):
        base.initializeExpr(self)
        for f in arguments:
            assert isinstance(f, Expression)
        self.arguments = arguments

    def addAllTypeVariables(self, s):
        for f in self.arguments: f.addAllTypeVariables(s)

class CallExpr(Expression):
    """A function call."""

    def __init__(self, operator, arguments, base = ExprInit.default):
        base.initializeExpr(self)
        assert isinstance(operator, Expression)
        for arg in arguments:
            assert isinstance(arg, Expression)
        self.operator = operator
        self.arguments = arguments

    def addAllTypeVariables(self, s):
        self.operator.addAllTypeVariables(s)
        for arg in self.arguments: arg.addAllTypeVariables(s)

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

    def addAllTypeVariables(self, s):
        self.argument.addAllTypeVariables(s)
        self.ifTrue.addAllTypeVariables(s)
        self.ifFalse.addAllTypeVariables(s)

class FunExpr(Expression):
    """A lambda function"""
    def __init__(self, function, base = ExprInit.default):
        base.initializeExpr(self)
        assert isinstance(function, Function)
        self.function = function

    def addAllTypeVariables(self, s):
        self.function.addAllTypeVariables(s)

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

    def addAllTypeVariables(self, s):
        if self.parameter: self.parameter.addAllTypeVariables(s)
        self.rhs.addAllTypeVariables(s)
        self.body.addAllTypeVariables(s)

class LetrecExpr(Expression):
    """A set of function definitions"""
    def __init__(self, definitions, body, base = ExprInit.default):
        base.initializeExpr(self)
        for d in definitions: assert isinstance(d, FunctionDef)
        assert isinstance(body, Expression)
        self.definitions = definitions
        self.body = body

    def addAllTypeVariables(self, s):
        for d in self.definitions:
            d.addAllTypeVariables(s)
        self.body.addAllTypeVariables(s)

###############################################################################
# Functions

class FunctionDef(object):
    """
    A named function definition.

    If the function has type information, then the function name has a
    type scheme and the function's parameters and body carry type information.
    Type variables used in type scheme are also used in the function body.
    """
    def __init__(self, name, function):
        assert isinstance(name, Variable)
        assert isinstance(function, Function)
        self.name = name
        self.function = function

    def addAllTypeVariables(self, s):
        self.function.addAllTypeVariables(s)

class Function(object):
    """
    A function or lambda term.

    If the function has an explicit 'forall' annotation, the type
    variables from the list are given in 'qvars'.

    The optional parameters 'qvars' and 'annotation' are the type variables
    declared in a 'forall' annotation and the declared return type,
    respectively.
    """

    def __init__(self, mode, parameters, body,
                 qvars = None,
                 annotation = None):
        assert mode == EXPRESSION or mode == ITERATOR
        for p in parameters:
            assert isinstance(p, Parameter)
        assert isinstance(body, Expression)
        self.mode = mode
        self.parameters = parameters
        self.qvars = qvars
        self.body = body
        self.annotation = annotation

    def addAllTypeVariables(self, s):
        for p in self.parameters: p.addAllTypeVariables(s)
        self.body.addAllTypeVariables(s)

def exprFunction(parameters, body, qvars = None, annotation = None):
    "Create an expression function"
    return Function(EXPRESSION, parameters, body, qvars = qvars,
                    annotation = annotation)

def iterFunction(parameters, body, qvars = None, annotation = None):
    "Create an iterator function"
    return Function(ITERATOR, parameters, body, qvars = qvars,
                    annotation = annotation)

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

    def addAllTypeVariables(self, s):
        for d in self.iterDefinitions(): d.addAllTypeVariables(s)
