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

    def pretty(self):
        "Show as a pretty-printable object.  This calls showWorker."
        return self.showWorker(PyonTypeBase.PREC_OUTER,
                               list(self.freeVariables()))

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
        elif isinstance(self, (FunTy, TupleTy)):
            return ProjectedTyApp(self.getConstructor(), self.getArguments())
        elif isinstance(self, AppTy):
            # Collect all operands into a single ProjectedTyApp value
            op_type = self.operator.project()
            return ProjectedTyApp(op_type, self.arg)
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

class DictionaryTyCon(FirstOrderType):
    """
    The type of a class dictionary.  A class dictionary type is like a tuple,
    but its members may be polymorphic.  Functions that manipulate dictionary
    types are not first-order types.
    """
    def __init__(self, cls):
        assert isinstance(cls, hmtype.classes.Class)
        self.cls = cls

    def __eq__(self, other):
        if not isinstance(other, DictionaryTyCon): return False
        return self.cls == other.cls

    def __str__(self):
        return "Dict(" + self.cls.name + ")"

###############################################################################
# Type expressions

# Use one alphabetic character to represent a type variable
_tyVarNames = 'abcdefghijklmnopqrstuvwxyz'

class TyVar(FirstOrderType, unification.Variable):
    """
    A unifiable type variable.
    """

    def addFreeVariables(self, s):
        canon = self.canonicalize()
        if canon is not self: return canon.addFreeVariables(s)
        s.add(self)

    def showWorker(self, precedence, visible_vars):
        # Use this variable's position in the list to make a name
        canon = self.canonicalize()
        if canon is not self: return canon.showWorker(precedence, visible_vars)
        
        return _tyVarNames[visible_vars.index(self)]

    # Inherit 'rename' from unification.Variable
    rename = unification.Variable.rename

class EntTy(FirstOrderType, unification.Term):
    """
    A type consisting of a single entity.
    """
    def __init__(self, ent):
        assert isinstance(ent, TyEnt)
        self.entity = ent

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

class FunTy(FirstOrderType, unification.Term):
    """
    An n-ary function type.

    An n-ary function type is equivalent to an application of FunTyCon to
    n+1 arguments.  It's common enough to merit using a special form.
    """

    def __init__(self, dom, rng):
        assert isinstance(dom, list)
        for param in dom:
            assert isinstance(param, FirstOrderType)
        assert isinstance(rng, FirstOrderType)
        self.domain = dom
        self.range = rng

    def __eq__(self, other):
        if not isinstance(other, FunTy): return False
        return self.domain == other.domain and self.range == other.range

    def getConstructor(self):
        return FunTyCon(len(self.domain))

    def getParameters(self):
        return self.domain + [self.range]

    def addFreeVariables(self, s):
        for d in self.domain: d.addFreeVariables(s)
        self.range.addFreeVariables(s)

    def showWorker(self, precedence, in_scope_vars):
        PREC_FUN = PyonTypeBase.PREC_FUN

        def product(xs):
            # [ x_0, times, x_1, times ... times, x_N]
            last = None
            for x in xs:
                if last:
                    yield x
                    yield _TIMES
                last = x
            yield last

        dom_doc = pretty.space(list(product(x.showWorker(PREC_FUN, in_scope_vars)
                                            for x in self.domain)))
        rng_doc = self.range.showWorker(PREC_FUN - 1, in_scope_vars)
        fun_doc = pretty.space([dom_doc, "->", rng_doc])

        if precedence >= PREC_FUN: fun_doc = pretty.parens(fun_doc)
        return fun_doc

    def rename(self, mapping):
        """
        Apply a substitution to all type variables in this term.  A new
        type is returned.
        """
        return FunTy([x.rename(mapping) for x in self.domain],
                     self.range.rename(mapping))

class TupleTy(FirstOrderType, unification.Term):
    """
    A tuple type.

    fields:
      arguments : [TyEnt]
    """

    def __init__(self, args):
        self.arguments = args

    def __eq__(self, other):
        if not isinstance(other, TupleTy): return False
        return self.arguments == other.arguments

    def getConstructor(self):
        return TupleTyCon(len(self.arguments))

    def getParameters(self):
        return self.arguments

    def addFreeVariables(self, s):
        for t in self.arguments: t.addFreeVariables(s)

    def showWorker(self, precedence, visible_vars):
        PREC_OUTER = PyonTypeBase.PREC_OUTER
        fields = [p.showWorker(PREC_OUTER, visible_vars) for p in self.arguments]
        return pretty.parens(pretty.space(pretty.punctuate(',', fields)))

    def rename(self, mapping):
        return TupleTy([arg.rename(mapping) for arg in self.arguments])

class AppTy(FirstOrderType, unification.Term):
    """
    A type application.
    """

    def __init__(self, oper, arg):
        self.operator = oper
        self.argument = arg

    def __eq__(self, other):
        if not isinstance(other, AppTy): return False
        return self.operator == other.operator and \
            self.argument == other.argument

    def canonicalize(self):
        # Uncurry nested applications
        oper = self
        rev_args = []           # Store arguments in reverse order
        while isinstance(oper, AppTy):
            rev_args.append(oper.argument)
            oper = oper.operator

        # If operator is a FunTyCon or TupleTyCon, then replace with that type
        if isinstance(oper, FunTyCon):
            assert len(rev_args) == oper.arity + 1
            return FunTy(reversed(rev_args[1:]), rev_args[0])
        elif isinstance(oper, TupleTyCon):
            assert len(rev_args) == oper.numArguments
            rev_args.reverse()
            return TupleTy(rev_args)

        # Else, already in canonical form
        return self

    def getConstructor(self):
        return AppTyCon()

    def getParameters(self):
        return [self.operator, self.argument]

    def addFreeVariables(self, s):
        self.operator.addFreeVariables(s)
        self.argument.addFreeVariables(s)

    def showWorker(self, precedence, visible_vars):
        return _genericShowApplication(self.operator, [self.argument],
                                       precedence, visible_vars)

    def rename(self, mapping):
        """
        Apply a substitution to all type variables in this term.  A new
        type is returned.
        """
        return AppTy(self.operator.rename(mapping),
                     self.argument.rename(mapping))

def _genericShowApplication(operator, operands, precedence, visible_vars):
    """
    _genericShowApplication(type-or-string, type-list, int, vars) -> pretty
    Show a type application using juxtapoxition: operator arg1 arg2 .. argN.
    This is called from showWorker methods.
    """
    PREC_APP = PyonTypeBase.PREC_APP

    # Show operator and operands.  Application is left-associative.
    if isinstance(operator, str):
        operator_doc = operator
    else:
        operator_doc = operator.showWorker(PREC_APP - 1, visible_vars)
    args_doc = [a.showWorker(PREC_APP, visible_vars) for a in operands]

    # Concatenate and parenthesize
    doc = pretty.space([operator_doc] + args_doc)
    if precedence >= PREC_APP: doc = pretty.parens(doc)
    return doc

def typeApplication(oper, args):
    """
    typeApplication(type, type-list) -> type

    Construct an expression representing the application of a type to some
    type parameters.
    """
    t = oper
    for arg in args: t = AppTy(t, arg)
    return t
