
import pyon.types.hmtype as hmtype
import pyon.unification as unification

import gluon

noSourcePos = gluon.noSourcePos

def _convertTyVar(v):
    if not v.gluonVariable:
        # Create a Gluon variable for this variable
        if isinstance(v, hmtype.RigidTyVar) and v.name:
            label = gluon.pgmLabel("pyonfile", v.name)
            v.gluonVariable = gluon.mkNewVariable(label, gluon.TypeLevel)
        else:
            v.gluonVariable = gluon.mkNewAnonymousVariable(gluon.TypeLevel)

    return v.gluonVariable

def _constructorType(con):
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
    assert isinstance(ty, hmtype.FirstOrderType)

    ty = unification.canonicalize(ty)
    if isinstance(ty, (hmtype.TyVar, hmtype.RigidTyVar)):
        return gluon.mkVarE(noSourcePos, _convertTyVar(ty))

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

def convertType(ty):
    """
    convertType(first-order-type) -> gluon-type
    convertType(type-scheme)      -> gluon-type

    Convert a Pyon type to a gluon type.
    """
    if isinstance(ty, hmtype.FirstOrderType):
        return _convertFirstOrderType(ty)
    else:
        raise NotImplementedError
