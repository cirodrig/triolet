"""
Predefined Pyon variables, types, classes, and instances are defined in this
module.
"""

import pyon.ast.ast as ast
import pyon.types.hmtype as hm

def _stmtFunctionType(param_types, return_type):
    """
    stmtFunctionType(param-types, return-type) -> type
    Create the type (p1 -> p2 -> ... -> St r) of a statement function.
    """
    # Start with return type
    t = hm.AppTy(hm.EntTy(type_St), return_type)

    # Affix parameter types onto the return type, starting with the last
    rparam_types = list(param_types)
    rparam_types.reverse()
    for param_t in rparam_types: t = hm.FunTy(param_t, t)
    return t

def _iterFunctionType(param_types, return_type):
    """
    iterFunctionType(param-types, return-type) -> type
    Create the type (p1 -> p2 -> ... -> St r) of a statement function.
    """
    # Start with return type
    t = hm.AppTy(hm.EntTy(type_St), return_type)

    # Affix parameter types onto the return type, starting with the last
    rparam_types = list(param_types)
    rparam_types.reverse()
    for param_t in rparam_types: t = hm.FunTy(param_t, t)
    return t

def _makeClasses():
    "Create type classes."
    global class_Eq, class_Ord, class_Num, class_Traversable

    # class Eq a where
    #   (==) : a -> a -> St a
    #   (!=) : a -> a -> St a
    a = hm.TyVar()
    binary_scheme = hm.TyScheme([], hm.noConstraints,
                             _stmtFunctionType([a,a], a))
    member_Eq_EQ = hm.ClassMethod(oper_EQ, binary_scheme)
    member_Eq_NE = hm.ClassMethod(oper_NE, binary_scheme)
    class_Eq = hm.Class("Eq", a, hm.noConstraints,
                     [member_Eq_EQ, member_Eq_NE])

    # class Eq a => Ord a where
    #   (<) : a -> a -> St a
    #   (<=) : a -> a -> St a
    #   (>) : a -> a -> St a
    #   (>=) : a -> a -> St a
    a = hm.TyVar()
    binary_scheme = hm.TyScheme([], hm.noConstraints,
                             _stmtFunctionType([a,a], a))
    member_Ord_LT = hm.ClassMethod(oper_LT, binary_scheme)
    member_Ord_LE = hm.ClassMethod(oper_LE, binary_scheme)
    member_Ord_GT = hm.ClassMethod(oper_GT, binary_scheme)
    member_Ord_GE = hm.ClassMethod(oper_GE, binary_scheme)
    class_Ord = hm.Class("Ord", a,
                      hm.Constraints([hm.ClassPredicate(a, class_Eq)]),
                      [member_Ord_LT, member_Ord_LE, member_Ord_GT,
                       member_Ord_GE])

    # class Eq a => Num a where
    #   (+) : a -> a -> St a
    #   (-) : a -> a -> St a
    #   (*) : a -> a -> St a
    #   negate : a -> St a
    a = hm.TyVar()
    binary_scheme = hm.TyScheme([], hm.noConstraints,
                             _stmtFunctionType([a,a], a))
    unary_scheme = hm.TyScheme([], hm.noConstraints,
                            _stmtFunctionType([a], a))
    member_Num_ADD = hm.ClassMethod(oper_ADD, binary_scheme)
    member_Num_SUB = hm.ClassMethod(oper_SUB, binary_scheme)
    member_Num_MUL = hm.ClassMethod(oper_MUL, binary_scheme)
    member_Num_NEGATE = hm.ClassMethod(oper_NEGATE, unary_scheme)
    class_Num = hm.Class("Num", a,
                      hm.Constraints([hm.ClassPredicate(a, class_Eq)]),
                      [member_Num_ADD, member_Num_SUB, member_Num_MUL,
                       member_Num_NEGATE])

    # class Traversable t where
    #   foreach : t a -> It a
    t = hm.TyVar()
    a = hm.TyVar()
    foreach_scheme = hm.TyScheme([a], hm.noConstraints,
                                 _iterFunctionType([hm.AppTy(t, a)], a))
    member_Tra_foreach = hm.ClassMethod(oper_FOREACH, foreach_scheme)
    class_Traversable = hm.Class("Traversable", t, hm.noConstraints,
                              [member_Tra_foreach])


###############################################################################

# Builtin binary functions with no Pyon implementation
oper_EQ = ast.ANFVariable()
oper_NE = ast.ANFVariable()
oper_LT = ast.ANFVariable()
oper_LE = ast.ANFVariable()
oper_GT = ast.ANFVariable()
oper_GE = ast.ANFVariable()
oper_ADD = ast.ANFVariable()
oper_SUB = ast.ANFVariable()
oper_MUL = ast.ANFVariable()
oper_DIV = ast.ANFVariable()
oper_MOD = ast.ANFVariable()
oper_POWER = ast.ANFVariable()
oper_FLOORDIV = ast.ANFVariable()
oper_BITWISEAND = ast.ANFVariable()
oper_BITWISEOR = ast.ANFVariable()
oper_BITWISEXOR = ast.ANFVariable()

# Builtin unary functions with no Pyon implementation
oper_NEGATE = ast.ANFVariable()

# Translations of generators and list comprehensions
oper_LIST = ast.ANFVariable()    # Turn generator into list comprehension
oper_FOREACH = ast.ANFVariable() # Translation of 'for' generators
oper_GUARD = ast.ANFVariable()   # Translation of 'if' generators
oper_DO = ast.ANFVariable()      # Generator body

# Builtin primitive types
type_int = hm.TyCon("int")
type_float = hm.TyCon("float")
type_bool = hm.TyCon("bool")

# Builtin types for statements and iterators
type_St = hm.TyCon("St")
type_It = hm.TyCon("It")

# Define classes and instances.
# Each global identifier is initialized to None for reasons of documentation.
# Their actual values come from the call to _makeClasses().
class_Eq = None
class_Ord = None
class_Num = None
class_Traversable = None

_makeClasses()
