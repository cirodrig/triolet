
import pyon.pretty as pretty

import pyon.types.kind as kind
import pyon.types.types as hmtype
import pyon.unification as unification

import gluon

noSourcePos = gluon.noSourcePos

def _convertKind(k):
    if isinstance(k, kind.Star):
        return gluon.type_Pure
    elif isinstance(k, kind.Arrow):
        dom = _convertKind(k.domain)
        rng = _convertKind(k.range)
        return gluon.mkArrowE(noSourcePos, False, dom, rng)
    else:
        raise TypeError, type(k)

def _convertVariable(v):
    "_convertVariable(TyVar or RigidTyVar) -> gluon variable"
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
        gluon_con = gluon.getTupleCon(con.numArguments)
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
    "_convertFirstOrderType(FirstOrderType) -> gluon type"
    assert isinstance(ty, hmtype.FirstOrderType)

    ty = unification.canonicalize(ty)
    if isinstance(ty, (hmtype.TyVar, hmtype.RigidTyVar)):
        return gluon.mkVarE(noSourcePos, _convertVariable(ty))

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
            domain = args[:-1]
            range = args[-1]

            # Make the domain a tuple
            fun_domain = gluon.mkConAppE(noSourcePos,
                                         gluon.getTupleCon(len(domain)),
                                         map(_convertFirstOrderType, domain))
            fun_range = _convertFirstOrderType(range)

            return gluon.mkArrowE(noSourcePos, False, fun_domain, fun_range)

        # Other things translate as type application
        oper = _convertFirstOrderType(operator)
        args = map(_convertFirstOrderType, args)
        return gluon.mkAppE(noSourcePos, oper, args)

def _convertConstraint(cst):
    "_convertConstraint(ClassPredicate) -> gluon type"
    # Convert a constraint to the corresponding dictionary type
    assert isinstance(cst, hmtype.ClassPredicate)

    ty = _convertFirstOrderType(cst.type)
    con = cst.typeClass.getGluonDictionaryCon()
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
                                      gluon.getTupleCon(num_constraints),
                                      map(_convertConstraint, scm.constraints))
        gluon_type = gluon.mkArrowE(noSourcePos, False, dict_params,
                                    gluon_type)

    # For each qvar, add a dependent type parameter
    for v in reversed(scm.qvars):
        gluon_type = gluon.mkFunE(noSourcePos, False, _convertVariable(v),
                                  _convertKind(v.getKind()), gluon_type)

    return gluon_type

def convertType(ty):
    """
    convertType(first-order-type) -> gluon-type
    convertType(type-scheme)      -> gluon-type

    Convert a Pyon type to a gluon type.
    """
    if isinstance(ty, hmtype.FirstOrderType):
        return _convertFirstOrderType(ty)
    if isinstance(ty, hmtype.TyScheme):
        return _convertTyScheme(ty)
    else:
        raise NotImplementedError
