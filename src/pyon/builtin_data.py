"""
Predefined Pyon variables, types, classes, and instances are defined in this
module.
"""

import pyon.pretty as pretty
import pyon.ast.ast as ast
import pyon.types.types as hm

functionType = hm.FunTy

def _makeClasses():
    "Create type classes."
    global class_Eq, class_Ord, class_Num, class_Traversable

    def cmp_scheme(a):
        return hm.TyScheme([], hm.noConstraints,
                           functionType([a,a], type_bool))
    # class Eq a where
    #   (==) : a -> a -> bool
    #   (!=) : a -> a -> bool
    a = hm.TyVar()
    def make_cmp_scheme_a(): return cmp_scheme(a)

    class_Eq = hm.Class("Eq", a, hm.noConstraints,
                        [hm.ClassMethod("__eq__", make_cmp_scheme_a),
                         hm.ClassMethod("__ne__", make_cmp_scheme_a)])

    # class Eq a => Ord a where
    #   (<) : a -> a -> bool
    #   (<=) : a -> a -> bool
    #   (>) : a -> a -> bool
    #   (>=) : a -> a -> bool
    class_Ord = hm.Class("Ord", a, [hm.ClassPredicate(None, a, class_Eq)],
                         [hm.ClassMethod("__lt__", make_cmp_scheme_a),
                          hm.ClassMethod("__le__", make_cmp_scheme_a),
                          hm.ClassMethod("__gt__", make_cmp_scheme_a),
                          hm.ClassMethod("__ge__", make_cmp_scheme_a)])

    # Instance declarations

    oper_Eq_EQ_int = ast.ANFVariable(name = "__eq__",
                                     type_scheme = cmp_scheme(type_int))
    oper_Eq_NE_int = ast.ANFVariable(name = "__ne__",
                                     type_scheme = cmp_scheme(type_int))
    hm.addInstance(class_Eq, [], hm.noConstraints, type_int,
                   [oper_Eq_EQ_int, oper_Eq_NE_int])

    oper_Eq_EQ_float = ast.ANFVariable(name = "__eq__",
                                       type_scheme = cmp_scheme(type_float))
    oper_Eq_NE_float = ast.ANFVariable(name = "__ne__",
                                       type_scheme = cmp_scheme(type_float))
    hm.addInstance(class_Eq, [], hm.noConstraints, type_float,
                   [oper_Eq_EQ_float, oper_Eq_NE_float])

    oper_Ord_LT_int = ast.ANFVariable(name = "__lt__",
                                     type_scheme = cmp_scheme(type_int))
    oper_Ord_LE_int = ast.ANFVariable(name = "__le__",
                                     type_scheme = cmp_scheme(type_int))
    oper_Ord_GT_int = ast.ANFVariable(name = "__gt__",
                                     type_scheme = cmp_scheme(type_int))
    oper_Ord_GE_int = ast.ANFVariable(name = "__ge__",
                                     type_scheme = cmp_scheme(type_int))
    hm.addInstance(class_Ord, [], hm.noConstraints, type_int,
                   [oper_Ord_LT_int, oper_Ord_LE_int,
                    oper_Ord_GT_int, oper_Ord_GE_int])

    oper_Ord_LT_float = ast.ANFVariable(name = "__lt__",
                                        type_scheme = cmp_scheme(type_float))
    oper_Ord_LE_float = ast.ANFVariable(name = "__le__",
                                        type_scheme = cmp_scheme(type_float))
    oper_Ord_GT_float = ast.ANFVariable(name = "__gt__",
                                        type_scheme = cmp_scheme(type_float))
    oper_Ord_GE_float = ast.ANFVariable(name = "__ge__",
                                        type_scheme = cmp_scheme(type_float))
    hm.addInstance(class_Ord, [], hm.noConstraints, type_float,
                   [oper_Ord_LT_float, oper_Ord_LE_float,
                    oper_Ord_GT_float, oper_Ord_GE_float])

#     # class Eq a => Num a where
#     #   (+) : a -> a -> St a
#     #   (-) : a -> a -> St a
#     #   (*) : a -> a -> St a
#     #   negate : a -> St a
#     a = hm.TyVar()
#     binary_scheme = hm.TyScheme([], hm.noConstraints,
#                              _stmtFunctionType([a,a], a))
#     unary_scheme = hm.TyScheme([], hm.noConstraints,
#                             _stmtFunctionType([a], a))
#     member_Num_ADD = hm.ClassMethod(oper_ADD, binary_scheme)
#     member_Num_SUB = hm.ClassMethod(oper_SUB, binary_scheme)
#     member_Num_MUL = hm.ClassMethod(oper_MUL, binary_scheme)
#     member_Num_NEGATE = hm.ClassMethod(oper_NEGATE, unary_scheme)
#     class_Num = hm.Class("Num", a,
#                       hm.Constraints([hm.ClassPredicate(a, class_Eq)]),
#                       [member_Num_ADD, member_Num_SUB, member_Num_MUL,
#                        member_Num_NEGATE])

#     # class Traversable t where
#     #   foreach : t a -> It a
#     t = hm.TyVar()
#     a = hm.TyVar()
#     foreach_scheme = hm.TyScheme([a], hm.noConstraints,
#                                  _iterFunctionType([hm.AppTy(t, a)], a))
#     member_Tra_foreach = hm.ClassMethod(oper_FOREACH, foreach_scheme)
#     class_Traversable = hm.Class("Traversable", t, hm.noConstraints,
#                               [member_Tra_foreach])


def create_type_schemes():
    global _unaryScheme, _binaryScheme, _compareScheme, _binaryIntScheme
    a = hm.TyVar()
    _unaryScheme = hm.TyScheme([a], hm.noConstraints, functionType([a], a))
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

_makeClasses()

# Builtin binary functions with no Pyon implementation
oper_EQ = class_Eq.getMethod("__eq__")
oper_NE = class_Eq.getMethod("__ne__")
oper_LT = class_Ord.getMethod("__lt__")
oper_LE = class_Ord.getMethod("__le__")
oper_GT = class_Ord.getMethod("__gt__")
oper_GE = class_Ord.getMethod("__ge__")
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
_list_type = hm.TyScheme.forall(1, lambda a: functionType([hm.AppTy(type_it, a)],
                                                      hm.AppTy(type_list, a)))
oper_LIST = ast.ANFVariable(name = "list", type_scheme = _list_type)

# Translation of 'for' generators
_foreach_type = hm.TyScheme.forall(3, lambda a, b, t: \
  functionType([hm.AppTy(t, a), functionType([a], hm.AppTy(type_it, b))], hm.AppTy(type_it, b)))
oper_FOREACH = ast.ANFVariable(name = "__foreach__", type_scheme = _foreach_type)

# Translation of 'if' generators
_guard_type = hm.TyScheme.forall(1, lambda a: \
  functionType([type_bool, a], hm.AppTy(type_it, a)))
oper_GUARD = ast.ANFVariable(name = "__guard__", type_scheme = _guard_type)

# Generator body
_do_type = hm.TyScheme.forall(1, lambda a: functionType([a], hm.AppTy(type_it, a)))
oper_DO = ast.ANFVariable(name = "__do__", type_scheme = _do_type)

# Builtin list functions
_reduce_type = hm.TyScheme.forall(2, lambda a, t: \
  functionType([functionType([a, a], a), hm.AppTy(t, a), a], a))
fun_reduce = ast.ANFVariable(name = "reduce", type_scheme = _reduce_type)

_reduce1_type = hm.TyScheme.forall(2, lambda a, t: \
  functionType([functionType([a, a], a), hm.AppTy(t, a)], a))
fun_reduce1 = ast.ANFVariable(name = "reduce1", type_scheme = _reduce1_type)

_zip_type = hm.TyScheme.forall(4, lambda a, b, c, d: \
  functionType([hm.AppTy(c, a), hm.AppTy(d, b)], \
               hm.AppTy(type_it, hm.TupleTy([a, b]))))
fun_zip = ast.ANFVariable(name = "zip", type_scheme = _zip_type)

_iota_type = hm.TyScheme.forall(1, lambda t: functionType([], hm.AppTy(t, type_int)))
fun_iota = ast.ANFVariable(name = "iota", type_scheme = _iota_type)

const_undefined = ast.ANFVariable(name = "__undefined__", type_scheme = hm.TyScheme.forall(1, lambda a: a))

# Define classes and instances.
# Each global identifier is initialized to None for reasons of documentation.
# Their actual values come from the call to _makeClasses().
class_Num = None
class_Traversable = None

# The list of all builtin functions
BUILTIN_FUNCTIONS = [fun_reduce, fun_reduce1, fun_zip, fun_iota, const_undefined]
