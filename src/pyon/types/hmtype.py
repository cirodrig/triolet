"""
Hindley-Milner types with type classes.

First-order types (the subclasses of FirstOrderType) should only be inspected
by calling methods or after calling the canonicalize() method.
Type schemes are constructed with TyScheme.
Classes are members of the class Class.
"""

import unicodedata

import pyon.ast.ast as ast
import pyon.unification as unification
import pyon.pretty as pretty

_TIMES = unicodedata.lookup('MULTIPLICATION SIGN')

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
        t.freeVariables() -> set of TyVar

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

    def showWorker(self, precedence, visible_vars):
        """
        Show as a pretty-printable object.  The precedence is used to
        decide whether parentheses are needed.  The list of visible variables
        is used to produce human-readable variable names.
        """
        raise NotImplementedError

    def rename(self, mapping):
        """
        Apply a substitution to all type variables in this term.  This creates
        a new object; the original remains unchanged.
        """
        raise NotImplementedError

    def pretty(self, type_variables = None):
        "Show as a pretty-printable object.  This calls showWorker."
        if type_variables is None:
            type_variables = self.freeVariables()
        if isinstance(type_variables, set):
            type_variables = list(type_variables)
        else:
            assert isinstance(type_variables, list)

        return self.showWorker(PyonTypeBase.PREC_OUTER, type_variables)

class PyonType(PyonTypeBase):
    """
    A type.
    """
    pass

class FirstOrderType(PyonType):
    """
    A first-order type.
    """
    def project(self):
        "Project the head of this type into a Herbrand term."
        self = self.canonicalize()
        if isinstance(self, TyVar): return ProjectedTyVar(self)
        elif isinstance(self, EntTy): return ProjectedTyCon(self.entity)
        elif isinstance(self, AppTy):
            # Collect all operands into a single ProjectedTyApp value
            op_type = self.operator.project()
            return ProjectedTyApp(op_type, self.argument)
        else:
            raise TypeError, type(self)

class ProjectedType(object): pass

class ProjectedTyVar(ProjectedType):
    def __init__(self, v):
        self.variable = v

class ProjectedTyCon(ProjectedType):
    def __init__(self, entity):
        self.entity = entity

class ProjectedTyApp(ProjectedType):
    def __init__(self, operator, argument):
        assert isinstance(operator, ProjectedType)
        self.operator = operator
        self.argument = argument

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

class TyCon(TyEnt):
    """
    A named type constructor.
    """

    def __init__(self, name):
        self.name = name

    def __eq__(self, other):
        # Identity of type constructors is object identity
        return id(self) == id(other)

    def __str__(self):
        return self.name

class DictionaryTyCon(TyEnt):
    """
    The type of a class dictionary.  A class dictionary type is like a tuple,
    but its members may be polymorphic.  Functions that manipulate dictionary
    types are not first-order types.
    """
    def __init__(self, cls):
        # Cannot refer to classes due to module dependences
        # assert isinstance(cls, pyon.types.classes.Class)
        self.cls = cls

    def __eq__(self, other):
        if not isinstance(other, DictionaryTyCon): return False
        return self.cls == other.cls

    def __str__(self):
        return "Dict(" + self.cls.name + ")"

class AnnotatedTyCon(TyEnt):
    """
    A type to represent annotated type variable
    """
    def __init__(self, name):
        self.name = name

    def __eq__(self, other):
        # Equality of AnnotatedTyCon is by object identity
        return self is other

    def __str__(self):
        return "'" + self.name

###############################################################################
# Type expressions

# Use one alphabetic character to represent a type variable
_tyVarNames = 'abcdefghijklmnopqrstuvwxyz'

class TyVar(FirstOrderType, unification.Variable):
    """
    A unifiable type variable.
    """

    def __eq__(self, other):
        canon = self.canonicalize()
        if canon is not self:
            return canon == other

        if isinstance(other, TyVar):
            other = other.canonicalize()

        return self is other

    def addFreeVariables(self, s):
        canon = self.canonicalize()
        if canon is not self: return canon.addFreeVariables(s)
        s.add(self)

    def showWorker(self, precedence, visible_vars):
        # Use this variable's position in the list to make a name
        canon = self.canonicalize()
        if canon is not self: return canon.showWorker(precedence, visible_vars)

        # Find the _last_ occurence of the variable in the list
        index = len(visible_vars) - 1
        for v in reversed(visible_vars):
            if v is canon: return _tyVarNames[index]
            index -= 1
        raise IndexError, self

    # Inherit 'rename' from unification.Variable
    rename = unification.Variable.rename

class EntTy(FirstOrderType, unification.Term):
    """
    A type consisting of a single entity.
    """
    def __init__(self, ent):
        assert isinstance(ent, TyEnt)
        self.entity = ent

    def __eq__(self, other):
        other = other.canonicalize()
        if not isinstance(other, EntTy): return False
        return self.entity == other.entity

    def addFreeVariables(self, s):
        # No free type variables
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
        canon = self.canonicalize()
        if canon is not self:
            return canon == other

        other = other.canonicalize()
        if not isinstance(other, AppTy): return False
        return self.operator == other.operator and \
            self.argument == other.argument

    def getConstructor(self):
        return AppTyCon()

    def getParameters(self):
        return [self.operator, self.argument]

    def addFreeVariables(self, s):
        self.operator.addFreeVariables(s)
        self.argument.addFreeVariables(s)

    def _uncurry(self):
        # Get all arguments from a sequence of applications
         oper = self
         rev_args = []           # Store arguments in reverse order
         while isinstance(oper, AppTy):
             rev_args.append(oper.argument)
             oper = oper.operator

         rev_args.reverse()
         return (oper, rev_args)

    def showWorker(self, precedence, visible_vars):
        (operator, arguments) = self._uncurry()

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

        return show(arguments, precedence, visible_vars)

    def rename(self, mapping):
        """
        Apply a substitution to all type variables in this term.  A new
        type is returned.
        """
        return AppTy(self.operator.rename(mapping),
                     self.argument.rename(mapping))

def _genericShowApplication(arguments, precedence, visible_vars):
    """
    _genericShowApplication(type-list, int, vars) -> pretty
    Show a type application using juxtapoxition: operator arg1 arg2 .. argN.
    This is called from showWorker methods.
    """
    PREC_APP = PyonTypeBase.PREC_APP

    # Show operator and operands.  Application is left-associative.
    operator_doc = arguments[0].showWorker(PREC_APP - 1, visible_vars)
    args_doc = [a.showWorker(PREC_APP, visible_vars) for a in arguments[1:]]

    # Concatenate and parenthesize
    doc = pretty.space([operator_doc] + args_doc)
    if precedence >= PREC_APP: doc = pretty.parens(doc)
    return doc

def _showFunction(args, precedence, in_scope_vars):
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

def _showTuple(args, precedence, visible_vars):
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

