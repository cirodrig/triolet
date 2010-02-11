
import itertools
import pyon.ast.ast
from pyon.types.hmtype import *
import pyon.types.schemes
import pyon.types.gluon_types
from pyon.types.placeholders import IdDerivation, InstanceDerivation
import gluon
import system_f

def _concatMap(f, sq):
    return itertools.chain(*[f(x) for x in sq])

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
    constraint : [ClassPredicate]
      Constraints that class members must satisfy
    methods: [ClassMethod]
      Declarations of the class's methods
    instances : [Instance]
      Instances of the class
    systemFClass : HsObject(PyonClass)
      The PyonClass value denoting this class
    systemFCon : HsObject(Con)
      The Gluon constructor denoting this class's dictionary type
    """

    def __init__(self, name, param, constraint, methods,
                 system_f_class, system_f_con):
        """
        Class(name, var, constraint, methods) -> new class
        """
        assert isinstance(param, TyVar)
        for c in constraint: assert isinstance(c, ClassPredicate)
        for t in methods: assert isinstance(t, ClassMethod)

        self.name = name
        self.parameter = param
        self.constraint = constraint
        self.methods = methods
        self.instances = []
        self.systemFClass = system_f_class
        self.systemFCon = system_f_con

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

    def getSystemFCon(self):
        "Get the System F dictionary type constructor for this class"
        return self.systemFCon

    def getSystemFClass(self):
        "Get the System F identifier for this class"
        return self.systemFClass

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
        c.getDictionaryType(delayed-gluon-type) -> delayed-gluon-type

        Get the type of a class method dictionary, given the types of the
        class's type parameter.
        """
        con_type = gluon.mkConE(gluon.noSourcePos, self.getSystemFCon())
        return gluon.mkAppE(gluon.noSourcePos, con_type, [type])

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
            constraints = [ClassPredicate(cls_var, cls)] + sig.constraints
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
    methods : [ObVariable]
      A list of instance methods.
      Each method is a globally defined function in System F.
      Each element of the list must match the corresponding list of class
      methods.
    """

    def __init__(self, qvars, constraints, cls, instance_type, methods):
        for v in qvars: assert isinstance(v, TyVar)
        for c in constraints: assert isinstance(c, ClassPredicate)
        assert isinstance(cls, Class)
        assert isinstance(instance_type, FirstOrderType)
        for m in methods: assert system_f.isExp(m)

        self.qvars = qvars
        self.constraints = constraints
        self.typeClass = cls
        self.instanceType = instance_type
        self.methods = methods

    def getMethodCode(self, superclasses):
        # Each superclass corresponds to one element of the constraint list
        if len(superclasses) != len(self.constraints):
            raise ValueError, "Wrong number of superclasses"

        if not len(superclasses):
            # If there are no superclasses, don't apply anything
            return self.methods
        else:
            # Apply method to superclasses
            return [system_f.mkCallE(m, superclasses)
                    for m in self.methods]


def addInstance(cls, qvars, constraints, instance_type, methods):
    inst = Instance(qvars, constraints, cls, instance_type, methods)
    cls.addInstance(inst)
    return inst

class ClassPredicate(PyonTypeBase):
    """
    A predicate stating that type @ty is a member of class @cls.
    ClassPredicate values are immutable (other than unification).

    fields:
    ty : Type
      A type.
    cls : Class
      The class the type inhabits.
    """
    def __init__(self, ty, cls):
        assert isinstance(cls, Class)
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
        t = unification.canonicalize(self.type)
        while True:
            if isinstance(t, TyVar): return True
            elif isinstance(t, EntTy): return False
            elif isinstance(t, AppTy): t = unification.canonicalize(t.operator)
            else: raise TypeError, type(t)

    def toHNF(self):
        """
        Return a list of head-normal-form predicates that are logically
        equivalent to this predicate.  The list may contain duplicates.

        An error is raised if this predicate cannot be converted to
        head-normal form.  If an error is raised, then it represents a
        type class error that should be reported to the user.
        """
        # Decide whether we're in head-normal form
        if self.isHNF(): return (IdDerivation(self), [self])

        # Perform context reduction
        ip = self.instancePredicates()
        if ip is None:
            instance_text = pretty.renderString(self.pretty())
            raise RuntimeError, "Cannot derive an instance for " + instance_text

        # Continue context reduction with superclasses
        (inst, constraints) = ip
        superclasses = []
        out_constraints = []
        for c in constraints:
            sc, local_constraints = c.toHNF()
            out_constraints += local_constraints
            superclasses.append(sc)

        return (InstanceDerivation(inst, superclasses,
                                   self.getDictionaryType()),
                out_constraints)

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
        ty = unification.canonicalize(self.type)

        # Common case shortcut: If this predicate pertains to a type
        # variable, we won't find any instances
        if isinstance(ty, TyVar): return None

        # For each instance
        for inst in self.typeClass.instances:
            # If this type does not match the instance head, go to next
            subst = unification.match(inst.instanceType, ty)
            if subst is None: continue

            # Get the constraints entailed by this type
            constraints = [c.rename(subst) for c in inst.constraints]
            return (inst, constraints)

        # Otherwise, no instances match
        return None

    def getDictionaryType(self):
        "Return the type of a class dictionary representing this instance"
        t = pyon.types.gluon_types.convertType(self.type)
        return self.typeClass.getDictionaryType(t)

    def addFreeVariables(self, s):
        self.type.addFreeVariables(s)

    def rename(self, substitution):
        return ClassPredicate(self.type.rename(substitution),
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
        # Is this predicate in the context?
        if p == predicate: return True

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
        if p == predicate: return True

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
    return simplify(list(_concatMap(lambda p: p.toHNF()[1], context)))

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

noConstraints = []

