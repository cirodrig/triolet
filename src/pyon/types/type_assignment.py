
import gluon
import system_f as sf

from pyon.types.placeholders import RecVarPlaceholder, DictPlaceholder
import pyon.types.hmtype as hmtype
import pyon.types.classes as classes
import pyon.types.schemes as schemes
import pyon.types.gluon_types as gluon_types

# This module needs to be separate to avoid module import cycles

class TypeAssignment(object):
    """
    A type assignment comprises a variable's Hindley-Milner type and how to
    translate the variable into System F form.  Type assignments are stored
    either as a field of a variable or in a type environment.

    The member function @instantiate characterizes type assignments.
    Calling @instantiate creates a new System F reference to the associated
    variable.  In the process, class constraints and placeholders may be
    created, which are returned for type inference to keep track of.  The
    created System F expression and its first-order type are returned.

    The @getFreeTypeVariables function returns the free type variables of
    the first-order type.

    The @getTypeScheme function returns the type assignment's
    (un-instantiated) type scheme.  This function should not be called on
    RecursiveAssignment instances, because a RecursiveAssignment stands
    for a variable whose scheme has not been inferred yet.
    """
    def getFreeTypeVariables(self):
        """
        a.getFreeTypeVariables(FreeVariableSet) -- updates the set
        Get the set of type variables referenced by this type assignment.
        """
        raise NotImplementedError, "'TypeAssignment' is an abstract base class"

    def getTypeScheme(self):
        """
        a.getTypeScheme() -> TyScheme

        Get this type assignment's type scheme.
        """
        raise NotImplementedError, "'TypeAssignment' is an abstract base class"

    def instantiate(self):
        """
        a.instantiate()
          -> ((constraints, placeholders), (sf.Exp, FirstOrderType))

        Create a System F use of this variable.
        """
        raise NotImplementedError, "'TypeAssignment' is an abstract base class"

class FirstOrderAssignment(TypeAssignment):
    """
    Assign a first-order type to a variable.  This is used for variables
    that are required to have first-order types by the type inference
    algorithm.
    """
    def __init__(self, type, value):
        assert isinstance(type, hmtype.FirstOrderType)
        self._type = type
        self._value = value

    def getFreeTypeVariables(self, s):
        self._type.addFreeTypeSymbols(s)

    def getTypeScheme(self):
        return schemes.TyScheme([], [], [], self._type)

    def instantiate(self):
        return (([], []), (self._value, self._type))

class PolymorphicAssignment(TypeAssignment):
    """
    Assign a type scheme to a variable.
    """
    def __init__(self, scheme, value):
        assert isinstance(scheme, schemes.TyScheme)
        self._scheme = scheme
        self._value = value

    def getFreeTypeVariables(self, s):
        self._scheme.addFreeTypeSymbols(s)

    def getTypeScheme(self):
        return self._scheme

    def instantiate(self):
        # Instantiate the type scheme
        (tyvars, constraints, first_order_type) = self._scheme.instantiate()

        # Apply the value to type and dictionary parameters
        placeholders, expr = \
            gluon_types.makeInstanceExpression(tyvars, constraints,
                                               self._value)

        return ((constraints, placeholders), (expr, first_order_type))

class RecursiveAssignment(TypeAssignment):
    """
    Assign a first-order type to a recursively defined variable.  The
    variable will later be assigned a polymorphic type.  The variable's
    System F expression is a placeholder, which will be replaced with
    an instantiation expression similar to what polymorphic variables have.
    """
    def __init__(self, variable, type):
        self._placeholder = RecVarPlaceholder(variable, type)

    def getFreeTypeVariables(self, s):
        self._placeholder.getFirstOrderType().addFreeTypeSymbols(s)

    def getTypeScheme(self):
        raise RuntimeError, \
            "Type scheme of recursive variable has not been inferred"

    def instantiate(self):
        ph = self._placeholder
        return (([], [ph]), (ph.getExpression(), ph.getFirstOrderType()))

class MethodAssignment(TypeAssignment):
    """
    Create a class method reference.  Types are inferred as for a
    polymorphic function.  A method selector System F expression is created.
    """
    def __init__(self, cls, method_index, method_type):
        assert isinstance(cls, classes.Class)
        assert isinstance(method_index, int)
        assert isinstance(method_type, schemes.TyScheme)
        self._class = cls
        self._methodIndex = method_index
        self._methodType = method_type

    def getFreeTypeVariables(self, s):
        self._methodType.addFreeTypeSymbols(s)

    def getTypeScheme(self):
        return self._methodType

    def instantiate(self):
        (tyvars, constraints, fotype) = self._methodType.instantiate()

        # This class is always the first in the constraint list
        this_cls_constraint = constraints[0]
        other_constraints = constraints[1:]
        assert this_cls_constraint.typeClass == self._class

        # The first type variable is the class variable
        other_tyvars = tyvars[1:]

        # Create a placeholder for the class dictionary
        dict_placeholder = DictPlaceholder(this_cls_constraint)

        # Create method selector expression
        selector_expr = \
            sf.mkMethodSelectE(self._class.getSystemFClass(),
                               gluon_types.convertType(this_cls_constraint.type),
                               self._methodIndex,
                               dict_placeholder.getExpression())

        # Apply type and dictionary parameters
        placeholders, expr = \
            gluon_types.makeInstanceExpression(other_tyvars,
                                               other_constraints,
                                               selector_expr)

        return ((constraints, placeholders + [dict_placeholder]),
                (expr, fotype))
