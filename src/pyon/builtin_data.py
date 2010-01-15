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

def functionType(param_types, return_type):
    # Affix parameter types onto the return type, starting with the last
    t = return_type
    for param_t in reversed(param_types): t = hm.FunTy(param_t, t)
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


def create_type_schemes():
    global _unaryScheme, _binaryScheme, _compareScheme, _binaryIntScheme
    a = hm.TyVar()
    _unaryScheme = hm.TyScheme([a], hm.noConstraints, hm.FunTy(a, a))
    _binaryScheme = hm.TyScheme([a], hm.noConstraints,
                                functionType([a,a], a))
    _compareScheme = hm.TyScheme([a], hm.noConstraints,
                                 functionType([a,a], type_bool))
    _binaryIntScheme = hm.TyScheme([], hm.noConstraints,
                                   functionType([type_int,type_int], type_int))

###############################################################################

# Builtin primitive types
tycon_int = hm.TyCon("int")
tycon_float = hm.TyCon("float")
tycon_bool = hm.TyCon("bool")
tycon_None = hm.TyCon("NoneType")
tycon_it = hm.TyCon("It")
tycon_list = hm.TyCon("list")

# Builtin types
type_int = hm.EntTy(tycon_int)
type_bool = hm.EntTy(tycon_bool)
type_float = hm.EntTy(tycon_float)
type_None = hm.EntTy(tycon_None)
type_it = hm.EntTy(tycon_it)
type_list = hm.EntTy(tycon_list)

create_type_schemes()

# Builtin binary functions with no Pyon implementation
oper_EQ = ast.ANFVariable(name = "__eq__", type_scheme = _compareScheme)
oper_NE = ast.ANFVariable(name = "__ne__", type_scheme = _compareScheme)
oper_LT = ast.ANFVariable(name = "__lt__", type_scheme = _compareScheme)
oper_LE = ast.ANFVariable(name = "__le__", type_scheme = _compareScheme)
oper_GT = ast.ANFVariable(name = "__gt__", type_scheme = _compareScheme)
oper_GE = ast.ANFVariable(name = "__ge__", type_scheme = _compareScheme)
oper_ADD = ast.ANFVariable(name = "__add__", type_scheme = _binaryScheme)
oper_SUB = ast.ANFVariable(name = "__sub__", type_scheme = _binaryScheme)
oper_MUL = ast.ANFVariable(name = "__mul__", type_scheme = _binaryScheme)
oper_DIV = ast.ANFVariable(name = "__div__", type_scheme = _binaryScheme)
oper_MOD = ast.ANFVariable(name = "__mod__", type_scheme = _binaryIntScheme)
oper_POWER = ast.ANFVariable(name = "__power__", type_scheme = _binaryScheme)
oper_FLOORDIV = ast.ANFVariable(name = "__floordiv__", type_scheme = _binaryScheme) # FIXME
oper_BITWISEAND = ast.ANFVariable(type_scheme = _binaryIntScheme)
oper_BITWISEOR = ast.ANFVariable(type_scheme = _binaryIntScheme)
oper_BITWISEXOR = ast.ANFVariable(type_scheme = _binaryIntScheme)

# Builtin unary functions with no Pyon implementation
oper_NEGATE = ast.ANFVariable(type_scheme = _unaryScheme)

# Translations of generators and list comprehensions

# Turn generator into list comprehension
_list_type = hm.TyScheme.forall(1, lambda a: hm.FunTy(hm.AppTy(type_it, a),
                                                      hm.AppTy(type_list, a)))
oper_LIST = ast.ANFVariable(name = "list", type_scheme = _list_type)

# Translation of 'for' generators
_foreach_type = hm.TyScheme.forall(3, lambda a, b, t: \
  functionType([hm.AppTy(t, a), hm.FunTy(a, hm.AppTy(type_it, b))], hm.AppTy(type_it, b)))
oper_FOREACH = ast.ANFVariable(name = "__foreach__", type_scheme = _foreach_type)

# Translation of 'if' generators
_guard_type = hm.TyScheme.forall(1, lambda a: \
  functionType([type_bool, a], hm.AppTy(type_it, a)))
oper_GUARD = ast.ANFVariable(name = "__guard__", type_scheme = _guard_type)

# Generator body
_do_type = hm.TyScheme.forall(1, lambda a: hm.FunTy(a, hm.AppTy(type_it, a)))
oper_DO = ast.ANFVariable(name = "__do__", type_scheme = _do_type)

# Define classes and instances.
# Each global identifier is initialized to None for reasons of documentation.
# Their actual values come from the call to _makeClasses().
class_Eq = None
class_Ord = None
class_Num = None
class_Traversable = None

# _makeClasses()
