
import itertools
import pyon.ast.ast
from pyon.types.hmtype import *
import pyon.types.schemes

def _concatMap(f, sq):
    return itertools.chain(*(f(x) for x in sq))

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
    methods: [ClassMethod]
      Declarations of the class's methods
    instances : [ClassInstance]
      Instances of the class
    """

    def __init__(self, name, param, constraint, methods):
        """
        Class(name, var, constraint) -> new class

        The constructed class is not valid; the remaining initalization is
        performed by defineClass(). 
        """
        assert isinstance(param, TyVar)
        for c in constraint: assert isinstance(c, ClassPredicate)
        for t in methods: assert isinstance(t, ClassMethod)

        self.name = name
        self.parameter = param
        self.constraint = constraint
        self.methods = methods
        self.instances = []

    def addInstance(self, inst):
        self.instances.append(inst)

    def getMethod(self, method):
        """
        c.getMethod(method-index) -> ANFVariable
        c.getMethod(method-name) -> ANFVariable
        Get the specified class member.
        """
        if isinstance(method, str):
            for m in self.methods:
                v = m.getVariable(self)
                if v.name == method:
                    return v
            raise IndexError, method
        elif isinstance(method, int):
            return self.methods[method].getVariable(self)
        else:
            raise TypeError, "argument must be string or int"
            

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

    def getMethodExpression(self, dictionary, method_name):
        """
        c.getMethodExpression(variable, variable) -> expression

        Given a variable that is a class instance dictionary, and a variable
        that is a method name, return an expression that extracts the class
        method from the dictionary.
        """
        raise NotImplementedError

    def getDictionaryType(self, type):
        """
        c.getDictionaryType(type) -> type

        Get the type of a class method dictionary, given the types of the
        class's type parameter.
        """
        return EntTy(DictionaryTyCon(self))

class ClassMethod(object):
    """
    A method of a type class.

    A method is specified by a name and type signature.  The type signature
    may refer to class variables.  The method's implementation is provided
    as part of each class instance.

    fields:
    name : String
      The variable name that Pyon programs use to invoke the method.
      The name is initialized to None.  It ahould be assigned before any
      objects look up this value.
    _signatureFun : () -> TyScheme
      A lambda function that returns the method's type signature.
      This is a lambda function because it may refer to a type object that
      has not been created yet.
    _signature : TyScheme
      The method's type signature.
    _variable : ANFVariable
      The ANF variable used to refer to this method.  This is created lazily.
      The variable's type is the type before type class desugaring.
    """
    def __init__(self, name, sig):
        self.name = name
        self._signatureFun = sig
        self._signature = None
        self._variable = None

    def getSignature(self):
        if self._signature: return self._signature
        sig = self._signature = self._signatureFun()
        return sig

    def getVariable(self, cls):
        v = self._variable
        if not v:
            # Extend the given signature with class constraints to get
            # the actual method signature
            sig = self.getSignature()
            cls_var = cls.parameter
            qvars = [cls_var] + sig.qvars
            constraints = [ClassPredicate(None, cls_var, cls)] + sig.constraints
            actual_sig = pyon.types.schemes.TyScheme(qvars, constraints,
                                                     sig.type)
            
            v = self._variable = \
                pyon.ast.ast.ANFVariable(self.name,
                                         type_scheme = actual_sig)
        return v

    def getTypeScheme(self):
        return self.getVariable().getTypeScheme()

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
    instanceType : FirstOrderType
      The types described by this Instance object.
    methods : [InstanceMethod]
      A list of instance methods.  Each element of the list must match
      the corresponding list of class methods.
    """

    def __init__(self, qvars, constraints, cls, instance_type, methods):
        for v in qvars: assert isinstance(v, TyVar)
        for c in constraints: assert isinstance(c, ClassPredicate)
        assert isinstance(cls, Class)
        assert isinstance(instance_type, FirstOrderType)

        self.qvars = qvars
        self.constraints = constraints
        self.typeClass = cls
        self.instanceType = instance_type
        self.methods = methods

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

def addInstance(cls, qvars, constraints, instance_type, methods):
    inst = Instance(qvars, constraints, cls, instance_type, methods)
    cls.addInstance(inst)
    return inst

class ClassPredicate(PyonTypeBase):
    """
    A predicate stating that type @ty is a member of class @cls.
    ClassPredicate values are immutable (other than unification).

    fields:
    dictVar : DictionaryVariable
      A variable representing a class dictionary for this type.
    ty : Type
      A type.
    cls : Class
      The class the type inhabits.
    """
    def __init__(self, dict_var, ty, cls):
        assert isinstance(cls, Class)
        self.dictVar = dict_var
        self.type = ty
        self.typeClass = cls

    def __eq__(self, other):
        if not isinstance(other, ClassPredicate): return False

        return self.typeClass is other.typeClass and self.type == other.type

    def match(self, other):
        if not isinstance(other, ClassPredicate):
            raise TypeError, type(other)

        # If classes don't match, then fail
        if self.typeClass is not other.typeClass: return None

        # Otherwise, match types
        return unification.match(self.type, other.type)

    def isHNF(self):
        "Return true if this predicate is in head-normal form"
        ty = self.type
        while True:
            prj = ty.project()
            if isinstance(prj, ProjectedTyVar): return True
            elif isinstance(prj, ProjectedTyCon): return False
            elif isinstance(prj, ProjectedTyApp): ty = prj.operator
            else: raise TypeError, type(ty)

    def toHNF(self):
        """
        Return a list of head-normal-form predicates that are logically
        equivalent to this predicate.  The list may contain duplicates.

        An error is raised if this predicate cannot be converted to
        head-normal form.  If an error is raised, then it represents a
        type class error that should be reported to the user.
        """
        # Decide whether we're in head-normal form
        if self.isHNF(): return [self]

        # Perform context reduction
        ip = self.instancePredicates()
        if ip is None:
            instance_text = pretty.renderString(self.pretty())
            raise RuntimeError, "Cannot derive an instance for " + instance_text

        (inst, constraints) = ip
        return list(_concatMap(lambda p: p.toHNF(), constraints))

    def superclassPredicates(self):
        """
        Returns an iterator over all superclass predicates entailed by
        this predicate.  The iterator may contain duplicates.
        """
        return _concatMap(lambda c: c.andSuperclassPredicates(),
                          self.typeClass.constraint)

    def andSuperclassPredicates(self):
        "Like superclassPredicates, except that the output includes self"
        yield self
        for p in self.superclassPredicates():
            assert isinstance(p, ClassPredicate)
            yield p

    def instancePredicates(self):
        """
        Try to satisfy this predicate with the known class instances.
        Returns the matching instance and a list of subgoals, or None if
        no instance matches.
        """
        ty = self.type.canonicalize()

        # Common case shortcut: If this predicate pertains to a type
        # variable, we won't find any instances
        if isinstance(ty, TyVar): return None

        # For each instance
        for inst in self.typeClass.instances:
            # If this type does not match the instance head, go to next
            subst = unification.match(ty, inst.instanceType)
            if subst is None: continue

            # Get the constraints entailed by this type
            constraints = [c.applySubstitution(subst)
                           for c in inst.constraints]
            return (inst, constraints)

        # Otherwise, no instances match
        return None

    def addFreeVariables(self, s):
        self.type.addFreeVariables(s)

    def rename(self, substitution):
        return ClassPredicate(self.dictVar,
                              self.type.rename(substitution),
                              self.typeClass)

    def showWorker(self, precedence, visible_vars):
        type_doc = self.type.showWorker(PyonTypeBase.PREC_APP, visible_vars)
        return pretty.space(self.typeClass.name, type_doc)

def entails(context, predicate):
    """
    entails(predicate-list, predicate) -> bool

    Returns true iff the conjunction of the predicates in the first list,
    together with class instances, implies the second predicate.
    """
    # Scan entire context, including superclasses, first
    for p in _concatMap(lambda c: c.andSuperclassPredicates(), context):
        # Try to match this predicate from the context against the
        # sought predicate
        substitution = p.match(predicate)
        if substitution is not None: return True

    # Then scan available instances 
    by_instance = predicate.instancePredicates()
    if by_instance is not None:
        # All subgoals must be entailed by the context
        _, constraints = by_instance
        for p in constraints:
            if not entails(context, p): return False

        return True
    # else
    return False

def entailsHNF(context, predicate):
    """
    entailsHNF(hnf-predicate-list, hnf-predicate) -> bool

    Returns true iff the conjunction of the predicates in the first list,
    together with class instances, implies the second predicate.
    This is a faster version of entailment that assumes that all input
    predicates are in head-normal form.
    """
    # Scan entire context, including superclasses, first
    for p in _concatMap(lambda c: c.andSuperclassPredicates(), context):
        # Try to match this predicate from the context against the
        # sought predicate
        substitution = p.match(predicate)
        if substitution is not None: return True

    return False

def simplify(context):
    """
    simplify(predicate-list) -> simplified predicate list
    """
    assert isinstance(context, list)

    # Simplified predicates will be put into a new list
    simplified = []

    # For each element of context
    for i in range(len(context)):
        p = context[i]

        # If this predicate is not entailed by the others, put it into the
        # simplified context
        if not entailsHNF(simplified + context[i+1:], p):
            simplified.append(p)

    return simplified

def reduce(context):
    """
    reduce(constraints) -> reduced constraints
    """
    return simplify(list(_concatMap(lambda p: p.toHNF(), context)))

def splitConstraints(constraints, free_vars, qvars):
    """
    splitConstraints(constraints, free-vars, quantified-vars)
        -> (retained-constraints, deferred-constraints)

    Split a set of constraints into a retained set and a deferred set.
    The retained set is added to a type scheme in which 'qvars' is the set
    of quantified variables.
    """
    constraints = reduce(constraints)

    # Partition constraints into retained and deferred sets
    deferred = []
    retained = []
    for p in constraints:
        constraint_vars = p.freeVariables()

        # If all of this constraint's variables are free in the environment,
        # then it is deferred
        for v in constraint_vars:
            if v not in free_vars: break
        else:
            deferred.append(p)
            continue

        # If all of this constraint's variables are in the environment or
        # qvars, then it is retained
        for v in constraint_vars:
            if v not in free_vars and v not in qvars: break
        else:
            retained.append(p)
            continue

        # Otherwise, apply defaulting rules
        print "Ambiguous constraint:", pretty.renderString(p.pretty())
        raise NotImplementedError, "defaulting"

    return (retained, deferred)

def unifyClassPredicates(p1, p2):
    # Not needed?
    assert p1.typeClass == p2.typeClass
    p1.type.unifyWith(p2.type)
    p1.dictVar.unifyWith(p2.dictVar)

noConstraints = []

