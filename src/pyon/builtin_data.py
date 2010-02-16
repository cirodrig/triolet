"""
Predefined Pyon variables, types, classes, and instances are defined in this
module.
"""

import gluon
import system_f as sf

import pyon.pretty as pretty
import pyon.ast.ast
import pyon.types.kind as kind
import pyon.types.stream_tag as stream_tag
import pyon.types.types as hm

_star = kind.Star()
_forall = hm.TyScheme.forall
_funType = hm.functionType
_anfVariable = pyon.ast.ast.ANFVariable

def _makeClasses():
    "Create type classes."
    global class_Eq, class_Ord, class_Num, class_Traversable

    def cmp_scheme(a):
        # Type scheme for comparsion operators:
        # forall a. a * a -> bool
        # ('a' is not a stream)
        return hm.TyScheme([], [], hm.noConstraints,
                           _funType([a,a], type_bool))

    def addPyonInstance(cls, qvars, constraints, type, members):
        # Add a class instance where all the members are constructors
        hm.addInstance(cls, qvars, constraints, type, map(sf.mkConE, members))

    # class Eq a where
    #   (==) : a -> a -> bool
    #   (!=) : a -> a -> bool
    a = hm.TyVar(_star, stream_tag.IsAction())
    scheme_1 = cmp_scheme(a)
    scheme_fn = lambda: scheme_1
    class_Eq = hm.Class("Eq", [], a, [],
                        [hm.ClassMethod("__eq__", scheme_fn),
                         hm.ClassMethod("__ne__", scheme_fn)],
                        sf.EqClass, sf.con_EqDict)
    del a, scheme_fn

    # class Eq a => Ord a where
    #   (<) : a -> a -> bool
    #   (<=) : a -> a -> bool
    #   (>) : a -> a -> bool
    #   (>=) : a -> a -> bool
    a = hm.TyVar(_star, stream_tag.IsAction())
    scheme_2 = cmp_scheme(a)
    scheme_fn = lambda: scheme_2
    class_Ord = hm.Class("Ord", [], a, [hm.ClassPredicate(a, class_Eq)],
                         [hm.ClassMethod("__lt__", scheme_fn),
                          hm.ClassMethod("__le__", scheme_fn),
                          hm.ClassMethod("__gt__", scheme_fn),
                          hm.ClassMethod("__ge__", scheme_fn)],
                         sf.OrdClass, sf.con_OrdDict)
    del a, scheme_fn

    # class Traversable (T : StreamTag) (t : * -> *) where
    #   foreach : t<T> a -> iter a
    T = stream_tag.StreamTagVar()
    t = hm.TyVar(kind.Arrow(_star, _star), T)

    a = hm.TyVar(_star, stream_tag.IsAction())
    scheme_3 = hm.TyScheme([], [a], [],
                           _funType([hm.AppTy(t, a)],
                                    hm.AppTy(type_iter, a)))
    del a
    scheme_fn = lambda: scheme_3
    class_Traversable = \
        hm.Class("Traversable", [T], t, [],
                 [hm.ClassMethod("__iter__", scheme_fn)],
                 sf.TraversableClass, sf.con_TraversableDict)
    del T, t, scheme_fn

    # Instance declarations
    addPyonInstance(class_Eq, [], [], type_int,
                    [sf.con_EQ_Int, sf.con_NE_Int])
    addPyonInstance(class_Eq, [], [], type_float,
                    [sf.con_EQ_Float, sf.con_NE_Float])

    b = hm.TyVar(_star)
    c = hm.TyVar(_star)
    addPyonInstance(class_Eq, [b, c],
                    [hm.ClassPredicate(b, class_Eq),
                     hm.ClassPredicate(c, class_Eq)],
                    hm.tupleType([b,c]),
                    [sf.con_EQ_Tuple2, sf.con_NE_Tuple2])
    del b, c

    addPyonInstance(class_Ord, [], hm.noConstraints, type_int,
                    [sf.con_LT_Int, sf.con_LE_Int,
                     sf.con_GT_Int, sf.con_GE_Int])

    addPyonInstance(class_Ord, [], hm.noConstraints, type_float,
                    [sf.con_LT_Float, sf.con_LE_Float,
                     sf.con_GT_Float, sf.con_GE_Float])

    addPyonInstance(class_Traversable, [], hm.noConstraints, type_iter,
                    [sf.con_TRAVERSE_Stream])
    addPyonInstance(class_Traversable, [], hm.noConstraints, type_list,
                    [sf.con_TRAVERSE_list])

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
    a = hm.TyVar(_star, stream_tag.IsAction())
    _unaryScheme = hm.TyScheme([], [a], hm.noConstraints, _funType([a], a))
    _binaryScheme = hm.TyScheme([], [a], hm.noConstraints, _funType([a,a], a))
    _compareScheme = hm.TyScheme([], [a], hm.noConstraints,
                                 _funType([a,a], type_bool))
    _binaryIntScheme = hm.TyScheme([], [], hm.noConstraints,
                                   _funType([type_int,type_int], type_int))

###############################################################################

# Builtin primitive types
tycon_int = hm.TyCon("int", _star, stream_tag.IsAction(),
                     gluon_constructor = gluon.con_Int)
tycon_float = hm.TyCon("float", _star, stream_tag.IsAction(),
                       gluon_constructor = gluon.con_Float)
tycon_bool = hm.TyCon("bool", _star, stream_tag.IsAction(),
                      gluon_constructor = sf.con_bool)
tycon_None = hm.TyCon("NoneType", _star, stream_tag.IsAction(),
                      gluon_constructor = sf.con_NoneType)
tycon_iter = hm.TyCon("iter", kind.Arrow(_star, _star),
                      stream_tag.IsStream(),
                      gluon_constructor = sf.con_Stream)
tycon_list = hm.TyCon("list", kind.Arrow(_star, _star),
                      stream_tag.IsAction(),
                      gluon_constructor = sf.con_list)

# Builtin types
type_int = hm.EntTy(tycon_int)
type_bool = hm.EntTy(tycon_bool)
type_float = hm.EntTy(tycon_float)
type_None = hm.EntTy(tycon_None)
type_iter = hm.EntTy(tycon_iter)
type_list = hm.EntTy(tycon_list)

create_type_schemes()

# Define classes and instances.
# Each global identifier is initialized to None for reasons of documentation.
# Their actual values come from the call to _makeClasses().
class_Eq = None
class_Ord = None
class_Num = None
class_Traversable = None

_makeClasses()

# Builtin binary functions with no Pyon implementation
oper_EQ = class_Eq.getMethod("__eq__")
oper_NE = class_Eq.getMethod("__ne__")
oper_LT = class_Ord.getMethod("__lt__")
oper_LE = class_Ord.getMethod("__le__")
oper_GT = class_Ord.getMethod("__gt__")
oper_GE = class_Ord.getMethod("__ge__")
oper_ADD = _anfVariable(name = "__add__", type_scheme = _binaryScheme)
oper_SUB = _anfVariable(name = "__sub__", type_scheme = _binaryScheme)
oper_MUL = _anfVariable(name = "__mul__", type_scheme = _binaryScheme)
oper_DIV = _anfVariable(name = "__div__", type_scheme = _binaryScheme)
oper_MOD = _anfVariable(name = "__mod__", type_scheme = _binaryIntScheme)
oper_POWER = _anfVariable(name = "__power__", type_scheme = _binaryScheme)
oper_FLOORDIV = _anfVariable(name = "__floordiv__", type_scheme = _binaryScheme) # FIXME
oper_BITWISEAND = _anfVariable(type_scheme = _binaryIntScheme)
oper_BITWISEOR = _anfVariable(type_scheme = _binaryIntScheme)
oper_BITWISEXOR = _anfVariable(type_scheme = _binaryIntScheme)
oper_ARROW = _anfVariable(type_scheme = _binaryScheme)

# Builtin unary functions with no Pyon implementation
oper_NEGATE = _anfVariable(type_scheme = _unaryScheme)

# Traversal
oper_ITER = class_Traversable.getMethod("__iter__")

# Translations of generators and list comprehensions
# use traversal along with 'cat_map', 'guard', and 'do'

# __cat_map__ : forall a b. (a -> iter b) * iter a -> iter b
_cat_map_type = \
    _forall([_star, _star],
            lambda a, b: _funType([_funType([a], hm.AppTy(type_iter, b)),
                                   hm.AppTy(type_iter, a)],
                                  hm.AppTy(type_iter, b)))
oper_CAT_MAP = _anfVariable(name = "__cat_map__",
                               type_scheme = _cat_map_type)

# __guard__ : forall a. bool * iter a -> iter a
_guard_type = _forall([_star], lambda a: \
                          _funType([type_bool, hm.AppTy(type_iter, a)],
                                   hm.AppTy(type_iter, a)))
oper_GUARD = _anfVariable(name = "__guard__", type_scheme = _guard_type)

# __do__ : forall a. a -> iter a
_do_type = _forall([_star], lambda a: _funType([a], hm.AppTy(type_iter, a)))
oper_DO = _anfVariable(name = "__do__", type_scheme = _do_type)

# The list-building operator
# list : forall t a. Traversable t => t a -> list a
T = stream_tag.StreamTagVar()
t = hm.TyVar(kind.Arrow(_star, _star), T)
a = hm.TyVar(_star, stream_tag.IsAction())
_list_type = hm.TyScheme([T], [t, a],
                         [hm.ClassPredicate(t, class_Traversable)],
                         _funType([hm.AppTy(t, a)], hm.AppTy(type_list, a)))
del T, t, a
fun_list = _anfVariable(name = "makelist", type_scheme = _list_type)

# Builtin list and iterator functions
# 'map', 'reduce', 'reduce1', 'zip', 'iota'

T = stream_tag.StreamTagVar()
t = hm.TyVar(kind.Arrow(_star, _star), T)
a = hm.TyVar(_star, stream_tag.IsAction())
b = hm.TyVar(_star, stream_tag.IsAction())
_map_type = hm.TyScheme([T], [t, a],
                        [hm.ClassPredicate(t, class_Traversable)],
                        _funType([_funType([a], b),
                                  hm.AppTy(t, a)],
                                 hm.AppTy(t, b)))
del T, t, a, b
fun_map = _anfVariable(name = "map", type_scheme = _map_type)

T = stream_tag.StreamTagVar()
t = hm.TyVar(kind.Arrow(_star, _star), T)
a = hm.TyVar(_star, stream_tag.IsAction())
_reduce_type = hm.TyScheme([T], [t, a],
                           [hm.ClassPredicate(t, class_Traversable)],
                           _funType([_funType([a, a], a),
                                     a,
                                     hm.AppTy(t, a)],
                                    a))
del T, t, a
fun_reduce = _anfVariable(name = "reduce", type_scheme = _reduce_type)

T = stream_tag.StreamTagVar()
t = hm.TyVar(kind.Arrow(_star, _star), T)
a = hm.TyVar(_star, stream_tag.IsAction())
_reduce1_type = hm.TyScheme([T], [t, a],
                            [hm.ClassPredicate(t, class_Traversable)],
                            _funType([_funType([a, a], a),
                                      hm.AppTy(t, a)],
                                     a))
del T, t, a
fun_reduce1 = _anfVariable(name = "reduce1", type_scheme = _reduce1_type)

T1 = stream_tag.StreamTagVar()
T2 = stream_tag.StreamTagVar()
s = hm.TyVar(kind.Arrow(_star, _star), T1)
t = hm.TyVar(kind.Arrow(_star, _star), T2)
a = hm.TyVar(_star, stream_tag.IsAction())
b = hm.TyVar(_star, stream_tag.IsAction())
_zip_type = hm.TyScheme([T1, T2], [s,t,a,b],
                        [hm.ClassPredicate(s, class_Traversable),
                         hm.ClassPredicate(t, class_Traversable)],
                        _funType([hm.AppTy(s, a), hm.AppTy(t, b)],
                                 hm.AppTy(type_iter, hm.tupleType([a, b]))))
del T1, T2, s, t, a, b
fun_zip = _anfVariable(name = "zip", type_scheme = _zip_type)

_iota_type = _forall([], lambda: _funType([], hm.AppTy(type_iter, type_int)))
fun_iota = _anfVariable(name = "iota", type_scheme = _iota_type)

T = stream_tag.StreamTagVar()
a = hm.TyVar(kind.Star(), T)
const_undefined = _anfVariable(name = "__undefined__",
                               type_scheme = hm.TyScheme([T], [a], [], a))
del T, a

# The list of all builtin functions
BUILTIN_FUNCTIONS = [fun_list, fun_reduce, fun_reduce1, fun_map, fun_zip,
                     fun_iota,
                     const_undefined]

# The list of all builtin constructors
BUILTIN_DATATYPES = [tycon_int, tycon_bool, tycon_float, tycon_None,
                     tycon_list, tycon_iter]

