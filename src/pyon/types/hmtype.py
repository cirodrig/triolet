"""
Hindley-Milner types with type classes.

First-order types (the subclasses of FirstOrderType) should only be inspected
by calling methods or after calling the canonicalize() method.
Type schemes are constructed with TyScheme.
Classes are members of the class Class.
"""

import pyon.ast.ast as ast
import pyon.unification as unification
import pyon.pretty as pretty

import pdb

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
        print "Error: called addFreeVariables()"
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

class FirstOrderType(PyonTypeBase):
    """
    A first-order type.
    """
    pass

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
    A function type constructor.
    """
    instance = None

    def __new__(cls):
        # This is a singleton class
        if cls.instance is None:
            FunTyCon.instance = t = TyEnt.__new__(cls)
            return t
        else: return cls.instance

    def __init__(self): pass

    def __eq__(self, other):
        # Singleton class, just compare object identity 
        return self is other

    def __str__(self):
        return "(->)"

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

    def rename(self, mapping):
        # First, canonicalize the variable.
        canon = self.canonicalize()
        if canon is not self: return canon.rename(mapping)

        # If this variable is a key in the mapping, then return its associated
        # value.  Otherwise, no change.
        try: return mapping[self]
        except KeyError: return self

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
    A function type.

    A function type is equivalent to an application of FunTyCon to two
    arguments.  It's common enough to merit using a special form.
    """

    def __init__(self, dom, rng):
        assert isinstance(dom, FirstOrderType)
        assert isinstance(rng, FirstOrderType)
        self.domain = dom
        self.range = rng

    def __eq__(self, other):
        if not isinstance(other, FunTy): return False
        return self.domain == other.domain and self.range == other.range

    def getConstructor(self):
        return FunTyCon()

    def getParameters(self):
        return [self.domain, self.range]

    def addFreeVariables(self, s):
        self.domain.addFreeVariables(s)
        self.range.addFreeVariables(s)

    def showWorker(self, precedence, in_scope_vars):
        PREC_FUN = PyonTypeBase.PREC_FUN
        dom_doc = self.domain.showWorker(PREC_FUN, in_scope_vars)
        rng_doc = self.range.showWorker(PREC_FUN - 1, in_scope_vars)
        fun_doc = pretty.space([dom_doc, "->", rng_doc])

        if precedence >= PREC_FUN: fun_doc = pretty.parens(fun_doc)
        return fun_doc

    def rename(self, mapping):
        """
        Apply a substitution to all type variables in this term.  A new
        type is returned.
        """
        return FunTy(self.domain.rename(mapping), self.range.rename(mapping))

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
            assert len(rev_args) == 2
            return FunTy(rev_args[1], rev_args[0])
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

###############################################################################
# Type classes

class Class(PyonTypeBase):
    """
    A type class.

    fields:
    name : string
      The class name
    param : TyVar
      A type variable that stands for an arbitrary member of the class
    constraint : Constraints
      Constraints that class members must satisfy
    methods : [ClassMethod]
      The class's methods
    """

    def __init__(self, name, param, constraints, methods):
        """
        Create a new class.
        """
        assert isinstance(param, TyVar)
        assert isinstance(constraints, Constraints)
        for m in methods:
            assert isinstance(m, ClassMethod)

        self.name = name
        self.parameter = param
        self.methods = methods
        self.instances = []

    def addInstance(self, inst):
        self.instances.append(inst)

    def findInstance(self, ty):
        """
        cls.findInstance(ty) -> (methods, constraints) or None

        Find a class instance that matches the given type.
        If an instance is found, return the instance's methods and a set of
        constraints.  If no instance can be found, then None is returned.
        """
        def return_result((methods, constraints)):
            # Add in the class's constraint set
            instantiation = instantiateVariables([self.param])
            return (methods,
                    self.constraints.rename(instantiation) * constraints)

        # Try each instance until a match is found
        for i in self.instances:
            result = i.matchWith(ty)
            if result is not None: return return_result(result)
        return None

class ClassMethod(PyonTypeBase):
    """
    A method of a type class.

    A method is specified by a name and type signature.  The type signature
    may refer to class variables.  The method's implementation is provided
    as part of each class instance.

    fields:
    name : ANFVariable
      The variable name that Pyon programs use to invoke the method.
    signature : TyScheme
      The method's type signature.
    """
    def __init__(self, name, sig):
        assert isinstance(name, ast.ANFVariable)
        assert isinstance(sig, TyScheme)
        self.name = name
        self.signature = sig

class Instance(PyonTypeBase):
    """
    An instance of a type class.

    fields:
    qvars : [TyVar]
      Universally quantified type variables.
    constraints : Constraints
      Constraints that types must satisfy to inhabit this instance.
    cls : Class
      The class that this is an instance of.
    instanceType : type
      The types described by this Instance object.
    methods : [InstanceMethod]
      A list of instance methods.  Each element of the list must match
      the corresponding list of class methods.
    """

    def __init__(self, qvars, constraints, cls, instance_type, methods):
        assert isinstance(cls, Class)
        for v in qvars: assert isinstance(v, TyVar)
        assert isinstance(c, Constraints)
        assert isinstance(methods, InstanceMethod)

        self.qvars = qvars
        self.constraints = constraints
        self.typeClass = cls
        self.instanceType = instance_type
        self.methods = methods
        self.instanceVariable = instance_variable

    def matchWith(self, ty):
        """
        inst.matchWith(t) -> (methods, constraints) or None

        Check whether type 't' matches this instance rule.  If so, then return
        a list of class methods and an extra constraint that
        must be satisfied.  If 't' does not match this instance declaration,
        return None."""
        # Attempt to unify this instance with the given type
        instantiation = instantiateVariables(self.qvars)
        try: unify(ty, param.rename(instantiation))
        except UnificationError: return None

        # Instantiate and return the methods and constraints
        methods = [m.rename(instantiation) for m in self.methods]
        constraints = self.constraints.rename(instantiation)
        return (methods, constraints)

class InstanceMethod(PyonTypeBase):
    """
    A method of a type class instance.

    fields:
    name : ANFVariable
      The variable name that Pyon programs use to invoke the method.  This
      should be the same as the corresponding ClassMethod name.
    func : Function
      The implementation of this instance.  This should have the same type
      as the type signature of the corresponding ClassMethod.
    """
    def __init__(self, name, func):
        assert isinstance(name. ast.ANFVariable)
        assert isinstance(func, ast.Function)
        self.name = name
        self.function = func

class ClassPredicate(PyonTypeBase):
    """
    A single-parameter type class constraint.
    ClassPredicate values are immutable.
    """
    def __init__(self, ty, cls):
        assert isinstance(cls, Class)
        self.type = ty
        self.typeClass = cls

class Constraints(PyonTypeBase):
    """
    A set of class constraints.  Constraints values are immutable.

    Constraint sets maintain the invariant that no member of the set is
    entailed by any other.
    """

    def __init__(self, sq = None):
        if sq:
            # Create a set of class constraints from 'sq', simplifying and
            # discarding redundancies.
            print "Not implemented: hmtype.Constraints.__init__"
            self.constraints = []
        else:
            self.constraints = []

    def addFreeVariables(self, s):
        # Not implemented
        pass

    def rename(self, mapping):
        """
        Apply a renaming to this constraint set.
        Raise an error if the renamed constraint set is unsatisfiable.
        """
        raise NotImplementedError

    def generalizeOver(self, variables):
        """
        s.generalizeOver(variable-list) -> (dependent set, free set)

        Generalize this constraint set over a set of variables.
        Return a constraint set that depends on the given variables and a
        constraint set that does not.  The union of the returned constraints
        is equal to the original set.
        """
        raise NotImplementedError

    def __mul__(self, other):
        """Compute the intersection of two class constraint sets by combining
        the constraints from each set and removing redundant constraints.
        A new object is returned."""
        raise NotImplementedError

noConstraints = Constraints()

###############################################################################
# Type schemes

def instantiateVariables(vars):
    """
    instantiateVariables(variable-list) -> mapping

    Instantiate some type variables.  Each variable is mapped to a fresh type
    variable, and the mapping is returned.
    """
    return dict((v, TyVar()) for v in vars)

class TyScheme(PyonTypeBase):
    """
    A type scheme: forall (qvars). (constraints) => (t)
    """

    def __init__(self, qvars, constraints, t):
        assert isinstance(constraints, Constraints)
        self.qvars = qvars
        self.constraints = constraints
        self.type = t

    @classmethod
    def forall(cls, num_vars, body, constraints = lambda *xs: noConstraints):
        """
        TyScheme.forall(int, make-body) -> new type scheme
        TyScheme.forall(int, make-body, make-constraints) -> new type scheme

        Create a new type scheme quantified over new variables.
        """
        vars = tuple(TyVar() for v in range(num_vars))
        t = apply(body, vars)
        csts = apply(constraints, vars)
        return cls(vars, csts, t)

    def rename(self, mapping):
        # Bound variables should never be renamed and variables should not be
        # shadowed
        for v in self.qvars:
            if v in mapping.keys():
                raise ValueError, "Attempt to rename variable bound by type scheme"

        # Rename variables in this type scheme
        return TyScheme(self.qvars,
                        self.constraints.rename(mapping),
                        self.type.rename(mapping))

    def showWorker(self, precedence, visible_vars):
        # Show as forall a b c. 
        var_list = [v.showWorker(PyonTypeBase.PREC_OUTER, visible_vars) \
            for v in self.qvars]
        var_doc = pretty.space(pretty.punctuate(',', var_list))
        quantifier = pretty.space("forall", pretty.abut(var_doc, '.'))
        monotype = self.type.showWorker(PyonTypeBase.PREC_FUN - 1,
                                        visible_vars + qvars)
        return pretty.linewr(quantifier, monotype, 2)

    def instantiate(self):
        """
        scheme.instantiate() -> type
        Instantiate a type scheme by creating fresh variables for each type.
        """
        # Rename each type variable to a fresh variable
        mapping = dict((v, TyVar()) for v in self.qvars)
        return self.type.rename(mapping)

    def addFreeVariables(self, s):
        # The type scheme's quantified variables must not be free
        assert not len(set.intersection(set(self.qvars), s))

        self.constraints.addFreeVariables(s)
        self.type.addFreeVariables(s)

        for v in self.qvars: s.discard(v)

def generalize(t, constraints):
    """
    generalize(t, constraints) -> (scheme, constraints)

    Generalize a type by quantifying over all free type variables.
    """
    (dependent_constraints, free_constraints) = \
        constraints.generalizeOver(t.freeVariables())

    scheme = TyScheme(list(t.freeVariables()), dependent_constraints, t)
    return (scheme, free_constraints)

