
from pyon.types.hmtype import *
import pyon.types.schemes

class DictionaryTy(PyonType):
    """
    The type of a class dictionary.  A class dictionary type is like a tuple,
    but its members may be polymorphic.  Because it contains type schemes, it
    is not a first-order type.
    """
    def __init__(self, cls):
        assert isinstance(cls, Class)
        self.cls = cls

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
    instances : [ClassInstance]
      Instances of the class
    dictionaryType : The type of a class dictionary
    """

    def __init__(self, name, param, constraint):
        """
        Class(name, var, constraint) -> new class

        The constructed class is not valid; the remaining initalization is
        performed by defineClass(). 
        """
        assert isinstance(param, TyVar)
        assert isinstance(constraints, Constraints)

        self.name = name
        self.parameter = param
        self.constraint = constraint
        self.dictionaryType = None # assigned by defineClass
        self.instances = []

    def setMethods(self, methods):
        for m in methods:
            assert isinstance(m, ClassMethod)
        if self.methods is not None:
            raise ValueError, "Class methods have already been assigned"
        self._methods = methods

    def getMethods(self):
        if self._methods is None:
            raise ValueError, "Class methods have not been assigned"
        return self._methods

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

def defineClass(name, param, constraint, method_defs):
    """
    defineClass(name, var, constraint, method-type-list) -> (class, methods)

    Define a type class.  The class is returned along with a list of generic
    class methods.
    """

    cls = Class(name, param, constraint)

    # Initialize methods and compute their types
    method_index = 0
    methods = []
    method_types = []
    for meth_vars, meth_constraint, fo_type in method_defs:

        # Method type definition:
        # forall param, meth_vars. (class dictionary type)
        #   let f = select method_index n_methods cls
        #   in f a b
        ast.Function(ast.EXPRESSION, [param] + meth_vars, body)
    dict_type = TupleTy([TySchemeTy(t) for t in method_types])

class ClassMethod(PyonTypeBase):
    """
    A method of a type class.

    A method is specified by a name and type signature.  The type signature
    may refer to class variables.  The method's implementation is provided
    as part of each class instance.

    fields:
    _name : ANFVariable
      The variable name that Pyon programs use to invoke the method.
      The name is initialized to None.  It ahould be assigned before any
      objects look up this value.
    signature : TyScheme
      The method's type signature.
    """
    def __init__(self, sig):
        assert isinstance(sig, TyScheme)
        self._name = None
        self.signature = sig

    def setName(self, name):
        assert isinstance(name, ast.ANFVariable)
        if self._name: raise ValueError, "Instance name is already assigned"
        self._name = name

    def getName(self):
        if not self._name: raise ValueError, "Instance name has not been assigned"
        return self._name

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

def unifyClassPredicates(p1, p2):
    assert p1.typeClass == p2.typeClass
    p1.type.unifyWith(p2.type)
    p1.dictVar.unifyWith(p2.dictVar)

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

