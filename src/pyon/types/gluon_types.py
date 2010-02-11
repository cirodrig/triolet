"""
The routines in this module convert Pyon's Hindley-Milner types and kinds to
Gluon types.

Conversion functions are called during type inference, but conversion occurs
after type inference.  Conversion actually passes a callback to Haskell via
the 'delayedType' function.  The callback is evaluated when the value is
demanded.  Delayed evaluation is necessary to observe the final result of
unification.
"""

import pyon.types.kind as kind
import pyon.types.hmtype as hmtype
import pyon.types.classes as classes
import pyon.types.schemes as schemes
import pyon.unification as unification
import pyon.types.placeholders

import gluon
import system_f

noSourcePos = gluon.noSourcePos

def mkPyonFunE(domain, range):
    """
    Create the Gluon function type corresponding to a Pyon function.
    The function's parameter types are gathered into a tuple.
    """
    dom = gluon.mkConAppE(noSourcePos,
                          system_f.getTupleCon(len(domain)),
                          domain)
    return gluon.mkArrowE(noSourcePos, False, dom, range)

def _makeFunctionType(domain, range):
    """
    Make the type of a function from @domain to @range.  The domain is a list
    of types, and is translated to a tuple type.
    """
    return mkPyonFunE(map(_convertFirstOrderType, domain),
                      _convertFirstOrderType(range))
    

def convertKind(k):
    """
    convertKind(Kind) -> gluon kind

    Convert a kind to a Gluon kind expression.
    """
    if isinstance(k, kind.Star):
        return gluon.type_Pure
    elif isinstance(k, kind.Arrow):
        dom = convertKind(k.domain)
        rng = convertKind(k.range)
        return gluon.mkArrowE(noSourcePos, False, dom, rng)
    else:
        raise TypeError, type(k)

def convertVariable(v):
    "convertVariable(TyVar or RigidTyVar) -> gluon variable"
    # If the variable has been unified with something, it's a type; we can't
    # create a Gluon variable out of it
    if unification.canonicalize(v) is not v:
        raise ValueError, "Cannot convert a variable that has been unified"

    if not v.gluonVariable:
        # Create a Gluon variable for this variable
        if isinstance(v, hmtype.RigidTyVar) and v.name:
            label = gluon.pgmLabel("pyonfile", v.name)
            v.gluonVariable = gluon.mkNewVariable(label, gluon.TypeLevel)
        else:
            v.gluonVariable = gluon.mkNewAnonymousVariable(gluon.TypeLevel)

    return v.gluonVariable

def _constructorType(con):
    "_constructorType(TyEnt) -> gluon type"
    assert isinstance(con, hmtype.TyEnt)

    # Put the constructor in gluon_con
    if isinstance(con, hmtype.TupleTyCon):
        gluon_con = system_f.getTupleCon(con.numArguments)
    elif isinstance(con, hmtype.TyCon):
        if con.gluonConstructor is None:
            raise ValueError, "Cannot translate constructor"
        gluon_con = con.gluonConstructor
    elif isinstance(con, hmtype.FunTyCon):
        raise ValueError, "Cannot translate an un-applied function type constructor"
    else:
        raise TypeError, type(con)

    return gluon.mkConE(noSourcePos, gluon_con)

def _convertFirstOrderType(ty):
    """
    _convertFirstOrderType(FirstOrderType) -> gluon type

    This must be called after unification is performed.  (Note that it calls
    'canonicalize', which produces a different result after unification).
    It is only called in a delayed manner by exported routines.
    """
    assert isinstance(ty, hmtype.FirstOrderType)

    ty = unification.canonicalize(ty)
    if isinstance(ty, (hmtype.TyVar, hmtype.RigidTyVar)):
        return gluon.mkVarE(noSourcePos, convertVariable(ty))

    elif isinstance(ty, hmtype.EntTy):
        return _constructorType(ty.entity)

    elif isinstance(ty, hmtype.AppTy):
        (operator, args) = ty.uncurry()
        operator = unification.canonicalize(operator)

        # Special translation for functions
        if isinstance(operator, hmtype.EntTy) and \
                isinstance(operator.entity, hmtype.FunTyCon):
            # Constructor must be fully applied
            assert 1 + operator.entity.arity == len(args)
            return _makeFunctionType(args[:-1], args[-1])

        # Other things translate as type application
        oper = _convertFirstOrderType(operator)
        args = map(_convertFirstOrderType, args)
        return gluon.mkAppE(noSourcePos, oper, args)

def _convertConstraint(cst):
    "_convertConstraint(ClassPredicate) -> gluon type"
    # Convert a constraint to the corresponding dictionary type
    assert isinstance(cst, classes.ClassPredicate)

    ty = _convertFirstOrderType(cst.type)
    con = cst.typeClass.getSystemFCon()
    return gluon.mkConAppE(noSourcePos, con, [ty])

def _convertTyScheme(scm):
    "_convertTyScheme(TyScheme) -> gluon type"
    # Start at the result-end of the type and work backwards, adding
    # parameter types
    gluon_type = _convertFirstOrderType(scm.type)

    # If there are constraints, add a tuple of dictionary parameters
    if scm.constraints:
        num_constraints = len(scm.constraints)

        dict_params = gluon.mkConAppE(noSourcePos,
                                      system_f.getTupleCon(num_constraints),
                                      map(_convertConstraint, scm.constraints))
        gluon_type = gluon.mkArrowE(noSourcePos, False, dict_params,
                                    gluon_type)

    # For each qvar, add a dependent type parameter
    for v in reversed(scm.qvars):
        gluon_type = gluon.mkFunE(noSourcePos, False, convertVariable(v),
                                  convertKind(v.getKind()), gluon_type)

    return gluon_type

def convertType(ty):
    """
    convertType(first-order-type) -> gluon-type
    convertType(type-scheme)      -> gluon-type

    Convert a Pyon type to a gluon type.
    """
    if isinstance(ty, hmtype.FirstOrderType):
        return gluon.delayedType(lambda: _convertFirstOrderType(ty))
    if isinstance(ty, schemes.TyScheme):
        return gluon.delayedType(lambda: _convertTyScheme(ty))
    else:
        raise TypeError, type(ty)

def instantiate(make_expr, scm):
    """
    instantiate((hmtype.FirstOrderType -> system_f.Expression), TyScheme)
        -> ((constraints, placeholders),
            (system_f.Expression, hmtype.FirstOrderType))

    Given an expression whose Hindley-Milner type is a type scheme, create
    code that represents an instantiation of the type scheme.  Return the code
    together with a list of constraints and placeholders.
    """
    # Append placeholders to this list as they are created
    placeholders = []

    (tyvars, constraints, first_order_type) = scm.instantiate()
    expr = make_expr(first_order_type)

    # For each type parameter, apply the instantiated type to a placeholder
    # type.  After type inference completes, these will be the actual type
    # parameters.
    for tv in tyvars:
        expr = system_f.mkTyAppE(expr, convertType(tv))

    # If there are constraints, then create a call expression for the
    # dictionary parameters
    if constraints:
        # For each constraint, make a dictionary parameter placeholder
        dict_placeholders = map(pyon.types.placeholders.DictPlaceholder,
                                constraints)
        dict_params = [p.getExpression() for p in dict_placeholders]
        placeholders.extend(dict_placeholders)

        # Apply the expression to all dictionary parameters
        expr = system_f.mkCallE(expr, dict_params)

    return ((constraints, placeholders), (expr, first_order_type))
