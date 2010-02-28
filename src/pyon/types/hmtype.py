"""
Hindley-Milner types with type classes.

First-order types (the subclasses of FirstOrderType) should only be inspected
by calling methods or after calling the canonicalize() method.
Type schemes are constructed with TyScheme.
Classes are members of the class Class.
"""

import unicodedata

import pyon.types.kind as kind
import pyon.types.stream_tag as stream_tag
from pyon.types.stream_tag import StreamTag
import pyon.unification as unification
import pyon.pretty as pretty

_TIMES = unicodedata.lookup('MULTIPLICATION SIGN')

class FreeVariableSet(object):
    def __init__(self, *argl, **argd):
        if len(argl) == 1 and len(argd) == 0:
            arg = argl[0]
            assert isinstance(arg, FreeVariableSet)
            self._variables = set(arg._variables)
            self._streamTags = set(arg._streamTags)
        elif len(argl) == 0:
            self._variables = set()
            self._streamTags = set()
            while argd:
                k, v = argd.popitem()
                if k == 'variables':
                    self._variables = set(v)
                elif k == 'stream_tags':
                    self._streamTags = set(v)
                else:
                    raise TypeError, "Invalid keyword argument"
        else:
            raise TypeError, "Too many arguments"

    def __contains__(self, x):
        if isinstance(x, (TyVar, RigidTyVar)):
            return x in self._variables
        elif isinstance(x, StreamTag):
            return x in self._streamTags
        else:
            raise TypeError, type(x)

    def addTyVar(self, v):
        assert isinstance(v, (TyVar, RigidTyVar))
        self._variables.add(v)

    def addStreamTagVar(self, v):
        assert isinstance(v, StreamTag)
        self._streamTags.add(v)

    def discardTyVar(self, v):
        assert isinstance(v, (TyVar, RigidTyVar))
        self._variables.discard(v)

    def discardStreamTagVar(self, v):
        assert isinstance(v, StreamTag)
        self._streamTags.discard(v)

    def iterTyVars(self):
        return iter(self._variables)

    def iterStreamTags(self):
        return iter(self._streamTags)

    def difference(self, other):
        return FreeVariableSet(variables = self._variables.difference(other._variables),
                               stream_tags = other._streamTags.difference(self._streamTags))

    def union(self, other):
        return FreeVariableSet(variables = self._variables.union(other._variables),
                               stream_tags = other._streamTags.union(self._streamTags))

    def update(self, other):
        self._variables.update(other._variables)
        self._streamTags.update(other._streamTags)

class PyonTypeBase(object):
    """
    An interface for type-level Pyon data, including types, classes, and type
    schemes.  Methods related to type variables and type variable scopes are
    defined here.

    Subclasses of this class are immutable (except for mutations due to
    unification.)
    """

    # Precedences, for showing
    PREC_OUTER = -1
    PREC_FORALL = 0
    PREC_FUN = 1
    PREC_APP = 2

    def freeVariables(self):
        """
        t.freeVariables() -> set

        Get the set of free type variables in this object.  This returns
        a new set that the caller may modify.
        """
        s = set()
        self.addFreeVariables(s)
        return s

    def addFreeVariables(self, s):
        """
        x.addFreeVariables(s) -- Add x's free variables to the set
        """
        raise NotImplementedError

    def freeTypeSymbols(self):
        """
        t.freeTypeSymbols() -> FreeVariableSet

        Get the set of free type variables in this object.  This returns
        a new set that the caller may modify.
        """
        s = FreeVariableSet()
        self.addFreeTypeSymbols(s)
        return s

    def addFreeTypeSymbols(self, s):
        """
        x.addFreeVariables(s) -- Add x's free variables to the set
        """
        raise NotImplementedError

    def showWorker(self, precedence, visible_vars):
        """
        Show as a pretty-printable object.  The precedence is used to
        decide whether parentheses are needed.  The list of visible variables
        is used to produce human-readable variable names.
        """
        raise NotImplementedError

    def rename(self, mapping):
        """
        Apply a substitution to all type variables in this term (including
        rigid and flexible type variables).  This creates a new object;
        the original remains unchanged.
        """
        raise NotImplementedError

    def pretty(self, type_variables = None):
        "Show as a pretty-printable object.  This calls showWorker."

        # Get the set of anonymous type variables
        if type_variables is None:
            type_variables = self.freeVariables()

        type_variables = [v for v in type_variables if isinstance(v, TyVar)]

        return self.showWorker(PyonTypeBase.PREC_OUTER, type_variables)

class PyonType(PyonTypeBase):
    """
    A type.
    """
    pass

class FirstOrderType(PyonType):
    """
    A first-order type.

    All types have a kind.  Types also have a stream tag, which
    determines how the type is translated to a Gluon type.  A type's
    stream tag determines the behavior of its fully applied type.
    """
    def getStreamTag(self):
        raise NotImplementedError

    def getKind(self):
        raise NotImplementedError

###############################################################################
# Atomic type-level entities

class TyEnt(object):
    """
    A type-level entity other than a unifiable type variable.
    Entities include type constructors and rigid type variables.
    A TyEnt should not be used as a type; use EntTy for that.
    """

    def __init__(self):
        raise NotImplementedError, "'TyEnt' is an abstract base class"

    def __eq__(self, other):
        raise NotImplementedError

    def __str__(self):
        "Show this entity as a pretty-printable document"
        raise NotImplementedError

    def getKind(self):
        raise NotImplementedError

class TupleTyCon(TyEnt):
    """
    A tuple type constructor.
    """

    def __init__(self, length):
        self.numArguments = length

    def __eq__(self, other):
        if not isinstance(other, TupleTyCon): return False
        return self.numArguments == other.numArguments

    def __str__(self):
        return "Tuple" + str(self.numArguments) + "Type"

    def getStreamTag(self):
        return stream_tag.IsAction() 

    def getKind(self):
        return kind.functionKind(self.numArguments)

class FunTyCon(TyEnt):
    """
    An n-ary function type constructor.
    """
    def __init__(self, arity):
        self.arity = arity

    def __eq__(self, other):
        if not isinstance(other, FunTyCon): return False
        return self.arity == other.arity

    def __str__(self):
        return "Fun" + str(self.arity) + "Type"

    def getStreamTag(self):
        return stream_tag.IsAction() 

    def getKind(self):
        return kind.functionKind(1 + self.arity)

class AppTyCon(TyEnt):
    """
    A dummy constructor term.  Unification sees the type application (f x) as
    an application (AppTyCon f x), where AppTyCon is a constructor and
    f and x are arguments.
    """
    instance = None

    def __new__(cls):
        # This is a singleton class
        if AppTyCon.instance is None:
            AppTyCon.instance = t = TyEnt.__new__(cls)
            return t
        else: return AppTyCon.instance

    def __init__(self): pass

    def __eq__(self, other):
        # Singleton class, just compare object identity 
        return self is other

    def __str__(self):
        # This should never actually be called
        return "@"

    def getStreamTag(self):
        raise ValueError, "Should not request the stream tag of 'AppTy' (it is not a real type constructor)"

    def getKind(self):
        raise ValueError, "Should not request the kind of 'AppTy' (it is not a real type constructor)"

class TyCon(TyEnt):
    """
    A named type constructor.
    """

    def __init__(self, name, con_kind, con_stream_tag, gluon_type = None):
        assert isinstance(con_kind, kind.Kind)

        # The stream tag must not be a variable
        assert isinstance(con_stream_tag, StreamTag)
        assert isinstance(con_stream_tag, unification.Term)

        self.gluonType = gluon_type
        self.name = name
        self._kind = con_kind
        self._streamTag = con_stream_tag

    def __eq__(self, other):
        # Identity of type constructors is object identity
        return id(self) == id(other)

    def __str__(self):
        return self.name

    def getStreamTag(self):
        return self._streamTag

    def getKind(self):
        return self._kind

###############################################################################
# Type expressions

# Use one alphabetic character to represent a type variable
_tyVarNames = 'abcdefghijklmnopqrstuvwxyz'

class TyVar(FirstOrderType, unification.Variable):
    """
    A unifiable type variable.
    """
    def __init__(self, _kind, _stream_tag = None):
        assert isinstance(_kind, kind.Kind)
        unification.Variable.__init__(self)
        self.gluonVariable = None
        self._kind = _kind
        self._streamTag = _stream_tag or stream_tag.StreamTagVar()

    def __eq__(self, other):
        canon = self.canonicalize()
        if canon is not self: return canon == other
        return self is unification.canonicalize(other)

    def getStreamTag(self):
        return self._streamTag

    def getKind(self):
        return self._kind

    def unifyWith(self, other):
        # First, compare and unify kinds and stream tags
        if self.getKind() != other.getKind():
            raise unification.UnificationError, "Kind mismatch"

        try: unification.unify(self.getStreamTag(), other.getStreamTag())
        except unification.UnificationError:
            raise unification.UnificationError, "Stream tag mismatch"

        # Then unify this variable with the other object
        return unification.Variable.unifyWith(self, other)

    def addFreeVariables(self, s):
        canon = self.canonicalize()
        if canon is not self:
            canon.addFreeVariables(s)
        else:
            s.add(self)

    def addFreeTypeSymbols(self, s):
        canon = self.canonicalize()
        if canon is not self:
            canon.addFreeTypeSymbols(s)
        else:
            s.addTyVar(self)
            if isinstance(self._streamTag, unification.Variable):
                s.addStreamTagVar(self._streamTag)

    def showWorker(self, precedence, visible_vars):
        # Use this variable's position in the list to make a name
        canon = self.canonicalize()
        if canon is not self: return canon.showWorker(precedence, visible_vars)

        # Find the _last_ occurence of the variable in the list
        index = len(visible_vars) - 1
        for v in reversed(visible_vars):
            if v is self:
                var_doc = _tyVarNames[index]
                break
            index -= 1
        else:
            raise IndexError, self

        # Add the stream tag
        stream_doc = self._streamTag.pretty()

        return pretty.abut([var_doc, '<', stream_doc, '>'])

    # Inherit 'rename' from unification.Variable
    rename = unification.Variable.rename

class RigidTyVar(FirstOrderType, unification.Term):
    """
    A rigid type variable.  Rigid type variables can be generalized over
    like type variables, but cannot be unified.
    """
    def __init__(self, name, _kind = kind.Star()):
        self.name = name
        self.gluonVariable = None
        self._streamTag = stream_tag.StreamTagVar()
        self._kind = _kind

    def __eq__(self, other):
        return self is other

    def __str__(self):
        return "'" + self.name

    def getStreamTag(self):
        return self._streamTag

    def getKind(self):
        return self._kind

    def addFreeVariables(self, s):
        s.add(self)

    def addFreeTypeSymbols(self, s):
        s.addTyVar(self)
        if isinstance(self._streamTag, unification.Variable):
            s.addStreamTagVar(self._streamTag)

    def getConstructor(self):
        return self

    def getParameters(self):
        return []

    def showWorker(self, precedence, visible_vars):
        vardoc = str(self)

        # Add the stream tag
        stream_doc = self._streamTag.pretty()

        return pretty.abut([vardoc, '<', stream_doc, '>'])

    def rename(self, mapping):
        # Rename this variable
        return unification.canonicalize(mapping.get(self, self))

class EntTy(FirstOrderType, unification.Term):
    """
    A type consisting of a single entity.
    """
    def __init__(self, ent):
        assert isinstance(ent, TyEnt)
        self.entity = ent

    def __eq__(self, other):
        other = unification.canonicalize(other)
        if not isinstance(other, EntTy): return False
        return self.entity == other.entity

    def getStreamTag(self):
        return self.entity.getStreamTag()

    def getKind(self):
        return self.entity.getKind()

    def addFreeVariables(self, s):
        # No free variables
        pass

    def addFreeTypeSymbols(self, s):
        # No free variables
        pass

    def getConstructor(self):
        return self.entity

    def getParameters(self):
        return []

    def showWorker(self, precedence, visible_vars):
        return str(self.entity)

    def rename(self, mapping):
        # No flexible type variables
        return self

def functionType(domain, range):
    """
    functionType(domain, range) -> first-order type

    Create the type of a function.
    """
    con = FunTyCon(len(domain))
    ty = EntTy(con)
    for t in domain: ty = AppTy(ty, t)
    ty = AppTy(ty, range)
    return ty

def tupleType(fields):
    """
    tupleType(fields) -> first-order type

    Create the type of a tuple.
    """
    con = TupleTyCon(len(fields))
    ty = EntTy(con)
    for t in fields: ty = AppTy(ty, t)
    return ty

class AppTy(FirstOrderType, unification.Term):
    """
    A type application.
    """

    def __init__(self, oper, arg):
        assert isinstance(oper, FirstOrderType)
        assert isinstance(arg, FirstOrderType)
        self.operator = oper
        self.argument = arg

    def __eq__(self, other):
        other = unification.canonicalize(other)
        if not isinstance(other, AppTy): return False
        return self.operator == other.operator and \
            self.argument == other.argument

    def getStreamTag(self):
        return self.operator.getStreamTag()

    def getKind(self):
        op_k = self.operator.getKind()
        if isinstance(op_k, kind.Arrow): return op_k.range
        else:
            raise ValueError, "Kind error in type application"

    def getConstructor(self):
        return AppTyCon()

    def getParameters(self):
        return [self.operator, self.argument]

    def addFreeVariables(self, s):
        self.operator.addFreeVariables(s)
        self.argument.addFreeVariables(s)

    def addFreeTypeSymbols(self, s):
        self.operator.addFreeTypeSymbols(s)
        self.argument.addFreeTypeSymbols(s)

    def uncurry(self):
        """
        t.uncurry() -> (operator, argument-list)

        Deconstruct a type application into an operator and list of arguments.
        The returned types are not guaranteed to be in canonical form.
        """
        # Get all arguments from a sequence of applications
        oper = self
        rev_args = []           # Store arguments in reverse order
        while isinstance(oper, AppTy):
            rev_args.append(oper.argument)
            oper = oper.operator

        rev_args.reverse()
        return (oper, rev_args)

    def showWorker(self, precedence, visible_vars):
        (operator, arguments) = self.uncurry()

        # Show saturated function and tuple types differently
        if isinstance(operator, EntTy):
            if isinstance(operator.entity, FunTyCon) and \
                    len(arguments) == operator.entity.arity + 1:
                show = _showFunction
            elif isinstance(operator.entity, TupleTyCon) and \
                    len(arguments) == operator.entity.numArguments:
                show = _showTuple
            else:
                show = _genericShowApplication
        else:
            show = _genericShowApplication

        return show(operator, arguments, precedence, visible_vars)

    def rename(self, mapping):
        """
        Apply a substitution to all type variables in this term.  A new
        type is returned.
        """
        return AppTy(self.operator.rename(mapping),
                     self.argument.rename(mapping))

def _genericShowApplication(operator, arguments, precedence, visible_vars):
    """
    _genericShowApplication(type-list, int, vars) -> pretty
    Show a type application using juxtapoxition: operator arg1 arg2 .. argN.
    This is called from showWorker methods.
    """
    PREC_APP = PyonTypeBase.PREC_APP

    # Show operator and operands.  Application is left-associative.
    operator_doc = operator.showWorker(PREC_APP - 1, visible_vars)
    args_doc = [a.showWorker(PREC_APP, visible_vars) for a in arguments]

    # Concatenate and parenthesize
    doc = pretty.space([operator_doc] + args_doc)
    if precedence >= PREC_APP: doc = pretty.parens(doc)
    return doc

def _showFunction(operator, args, precedence, in_scope_vars):
    PREC_FUN = PyonTypeBase.PREC_FUN

    def product(xs):
        # [ x_0, times, x_1, times ... times, x_N]
        last = None
        for x in xs:
            if last:
                yield last
                yield _TIMES
            last = x
        yield last

    dom_doc = pretty.space(list(product(x.showWorker(PREC_FUN, in_scope_vars)
                                        for x in args[:-1])))
    rng_doc = args[-1].showWorker(PREC_FUN - 1, in_scope_vars)
    fun_doc = pretty.space([dom_doc, "->", rng_doc])

    if precedence >= PREC_FUN: fun_doc = pretty.parens(fun_doc)
    return fun_doc

def _showTuple(operator, args, precedence, visible_vars):
    PREC_OUTER = PyonTypeBase.PREC_OUTER
    fields = [p.showWorker(PREC_OUTER, visible_vars) for p in args]
    return pretty.parens(pretty.space(pretty.punctuate(',', fields)))

def typeApplication(oper, args):
    """
    typeApplication(type, type-list) -> type

    Construct an expression representing the application of a type to some
    type parameters.
    """
    t = oper
    for arg in args: t = AppTy(t, arg)
    return t

