# parser_ast.py
#
# The AST data structures produced by the parser

import itertools

# Operator names
import pyon.ast.operators
import pyon.ast.ast as ast

class Variable(object):
    """Abstract base class of variables"""

    def __init__(self):
        raise NotImplementedError, "'Variable' is an abstract base class"

    def __eq__(self, other):
        raise NotImplementedError, "'Variable' is an abstract base class"

class PythonVariable(Variable):
    """A variable as determined by Python's name resolution rules"""
    def __eq__(self, other):
        return self.identifier == other.identifier

    def __init__(self, name, identifier = None, anf_variable = None):
        """
        Create a new Python variable.
        name: The name of the variable as it appears in the source code; None
          if the variable has no name.
        identifier: An integer that uniquely identifies this variable.  Two
          PythonVariable objects denote the same variable iff they have the
          same identifier.  If no identifer is given, a new integer will be
          assigned.
        anf_variable: If not None, this is the ANF variable corresponding to
          this variable in the parser output.  This is used for source code
          references to variables that are already in the IR, such as
          previously loaded modules.

        If two variables have the same identifier, they must also have the same
        ANF variable.  They are not required to have the same name.
        """
        assert isinstance(name, str)
        if identifier is None: identifier = PythonVariable.getNewID()
        assert isinstance(identifier, int)
        assert anf_variable is None or \
            isinstance(anf_variable, ast.ANFVariable)
        self.name = name
        self.identifier = identifier
        self.anfVariable = anf_variable

        # A map from python variable identifiers (uniquely identifying
        # Python variables) to SSA identifiers (uniquely identifying SSA
        # instances of Python variables).
        self.ssaVersionMap = {}         # Private to ANF conversion

    def hasANFVariable(self):
        return self.anfVariable is not None

    _nextID = 1

    @classmethod
    def setIDGenerator(cls, n):
        """
        Set the value of the counter used to assign new variable IDs.
        The value should be larger than any already assigned value.
        """
        assert type(n) is int
        PythonVariable._nextID = n

    @classmethod
    def getIDGenerator(cls):
        """
        Get the value of the counter used to assign new variable IDs.
        """
        return PythonVariable._nextID

    @classmethod
    def getNewID(cls):
        n = PythonVariable._nextID
        PythonVariable._nextID = n + 1
        return n

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

class Expression(object):
    """An abstract base class of expressions."""

    def __init__(self, arg):
        raise NotImplementedError, "'Expression' is an abstract base class"

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

class TupleExpr(Expression):
    """A tuple construction."""
    def __init__(self, args, base = ExprInit.default):
        base.initializeExpr(self)
        for e in args:
            assert isinstance(e, Expression)
        self.arguments = args

class UnaryExpr(Expression):
    """An application of a unary operator to an operand."""

    def __init__(self, op, arg, base = ExprInit.default):
        base.initializeExpr(self)
        assert isinstance(op, pyon.ast.operators.UnaryOp)
        assert isinstance(arg, Expression)
        self.operator = op
        self.argument = arg

class BinaryExpr(Expression):
    """An application of a binary operator to left and right operands."""

    def __init__(self, op, left, right, base = ExprInit.default):
        base.initializeExpr(self)
        assert isinstance(op, pyon.ast.operators.BinaryOp)
        assert isinstance(left, Expression)
        assert isinstance(right, Expression)
        self.operator = op
        self.left = left
        self.right = right

class ListCompExpr(Expression):
    """A list comprehension."""

    def __init__(self, iterator, base = ExprInit.default):
        base.initializeExpr(self)
        assert isinstance(iterator, ForIter) # Must start with 'for'
        self.iterator = iterator

class GeneratorExpr(Expression):
    """A generator expression."""

    def __init__(self, iterator, local_scope = None, base = ExprInit.default):
        base.initializeExpr(self)
        assert isinstance(iterator, ForIter) # Must start with 'for'
        self.iterator = iterator
        self.localScope = local_scope

class CallExpr(Expression):
    """A function call."""

    def __init__(self, operator, arguments, base = ExprInit.default):
        base.initializeExpr(self)
        assert isinstance(operator, Expression)
        for arg in arguments:
            assert isinstance(arg, Expression)
        self.operator = operator
        self.arguments = arguments

class CondExpr(Expression):
    """An if-else expression."""

    def __init__(self, argument, ifTrue, ifFalse, base = ExprInit.default):
        base.initializeExpr(self)
        assert isinstance(argument, Expression)
        assert isinstance(ifTrue, Expression)
        assert isinstance(ifFalse, Expression)
        self.argument = argument
        self.ifTrue = ifTrue
        self.ifFalse = ifFalse

class LambdaExpr(Expression):
    """A lambda function"""
    def __init__(self, parameters, body, base = ExprInit.default):
        base.initializeExpr(self)
        for p in parameters:
            assert isinstance(p, Parameter)
        assert isinstance(body, Expression)
        self.parameters = parameters
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
    """An iterating expression in a generator or comprehension."""
    def __init__(self):
        raise NotImplementedError, "'Iterator' is an abstract base class"

class ForIter(Iterator):
    """A 'for' term in an iterator."""
    
    def __init__(self, param, argument, body, base = IterInit.default):
        base.initializeIter(self)
        assert isinstance(param, Parameter)
        assert isinstance(argument, Expression)
        assert isinstance(body, Iterator)
        self.parameter = param
        self.argument = argument
        self.body = body

class IfIter(Iterator):
    """An 'if' term in an iterator."""

    def __init__(self, guard, body, base = IterInit.default):
        base.initializeIter(self)
        assert isinstance(guard, Expression)
        assert isinstance(body, Iterator)
        self.guard = guard
        self.body = body

class DoIter(Iterator):
    """The computational component in an iterator."""

    def __init__(self, body, base = IterInit.default):
        base.initializeIter(self)
        assert isinstance(body, Expression)
        self.body = body

###############################################################################
# Statements

class StmtInit(object):
    """An initializer for statement base types"""

    def __init__(self, astHandle = None):
        """Initialize this statement.

        astHandle: A handle to the original, printable AST data structure."""
        pass

    def initializeStmt(self, expr):
        """Initialize a 'Statement'.
        This is called from the statement's __init__ method."""
        return ()

# The default value of StmtInit
StmtInit.default = StmtInit()

class Statement(object):
    """An abstract base class of statements."""

    def __init__(self, arg):
        raise NotImplementedError, "'Statement' is an abstract base class"

class ExprStmt(Statement):
    """A statement consisting of a single expression"""

    def __init__(self, expr):
        assert isinstance(expr, Expression)
        self.expression = expr

class AssignStmt(Statement):
    """An assignment statement"""

    def __init__(self, lhs, expr):
        assert isinstance(lhs, Parameter)
        assert isinstance(expr, Expression)
        self.lhs = lhs
        self.expression = expr

class ReturnStmt(Statement):
    """A return statement"""

    def __init__(self, expr):
        assert isinstance(expr, Expression)
        self.expression = expr

class IfStmt(Statement):
    """An if-else statement"""

    def __init__(self, cond, if_true, if_false):
        assert isinstance(cond, Expression)
        for s in if_true:
            assert isinstance(s, Statement)
        for s in if_false:
            assert isinstance(s, Statement)
        self.cond = cond
        self.ifTrue = if_true
        self.ifFalse = if_false

class DefGroupStmt(Statement):
    """A group of function definitions"""

    def __init__(self, defs):
        for d in defs:
            assert isinstance(d, Function)
        self.definitions = defs

###############################################################################
# Functions

class Function(object):
    """
    A function definition.

    fields:
    name:
      The function's name
    qvars : [Variable] or None
      If the function declaration had a 'forall' annotation, this is the list
      of universally quantified variables that were declared.
    parameters: [Parameter]
      The function's parameters
    body:
      The function's body
    local_scope:
      The function's local variables.  (Not used.)
    """
    def __init__(self, name, qvars, parameters, annotation, body,
                 local_scope = None):
        assert isinstance(name, Variable)
        if qvars is not None:
            for v in qvars: assert isinstance(v, Variable)
        for p in parameters:
            assert isinstance(p, Parameter)
        for s in body:
            assert isinstance(s, Statement)
            assert annotation is None or isinstance(annotation, Expression)
        self.name = name
        self.qvars = qvars
        self.parameters = parameters
        self.annotation = annotation
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
                assert isinstance(d, Function)
        self.definitions = definitions

    def iterDefinitionGroups(self):
        """Get an iterator over the module's definition groups"""
        return iter(self.definitions)

    def iterDefinitions(self):
        """Get an iterator over all definitions in the module"""
        return itertools.chain(*self.definitions)
