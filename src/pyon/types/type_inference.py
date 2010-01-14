
import pyon.ast.ast as ast
import pyon
import pyon.pretty as pretty
# import pyon.builtin_data as builtin_data
import pyon.unification as unification
import hmtype
import pdb

def debug(msg):
    print msg
    pdb.set_trace()

ty_int = hmtype.EntTy(hmtype.TyCon("ty_int"))
ty_bool = hmtype.EntTy(hmtype.TyCon("ty_bool"))
ty_float = hmtype.EntTy(hmtype.TyCon("ty_float"))
ty_None = hmtype.EntTy(hmtype.TyCon("ty_None"))
type_it = hmtype.EntTy(hmtype.TyCon("ty_It"))
type_list = hmtype.EntTy(hmtype.TyCon("ty_list"))

def typrn(ty):
    pretty.render(ty.canonicalize().pretty())

def _FunctionType(param_types, return_type):
    """
    FunctionType(param-types, return-type) -> type
    Create the type (p1 -> p2 -> ... -> r) of a statement function.
    """
    assert isinstance(return_type, hmtype.PyonTypeBase)
    assert param_types != None
    assert return_type != None
    
    # Start with return type
    t = return_type

    # Affix parameter types onto the return type, starting with the last
    rparam_types = list(param_types)
    rparam_types.reverse()
    for param_t in rparam_types: t = hmtype.FunTy(param_t, t)
    return t

def _IterType(a):
    return hmtype.AppTy(type_it, a)

def _ListType(a):
    return hmtype.AppTy(type_list, a)

def _ForeachType(a, b):
    iter_b = _IterType(b)
    return _FunctionType(
        [hmtype.AppTy(hmtype.TyVar(), a), _FunctionType([a], iter_b)],
        iter_b)

def populateIntrinsicOperations(gamma):
    """
    oper_FLOORDIV = ast.ANFVariable()
    """

    # arith: a -> a -> a
    arith_opers = [
        pyon.builtin_data.oper_ADD,
        pyon.builtin_data.oper_SUB,
        pyon.builtin_data.oper_MUL,
        pyon.builtin_data.oper_DIV,
    ]
    for oper in arith_opers:
        a = hmtype.TyVar()
        ty_fn = _FunctionType([a, a], a)
        ty_scheme = hmtype.TyScheme([a], hmtype.noConstraints, ty_fn)
        gamma.add(oper, ty_scheme)

    # compare: a -> a -> bool
    compare_opers = [
        pyon.builtin_data.oper_EQ,
        pyon.builtin_data.oper_NE,
        pyon.builtin_data.oper_LT,
        pyon.builtin_data.oper_LE,
        pyon.builtin_data.oper_GT,
        pyon.builtin_data.oper_GE,
    ]
    for oper in compare_opers:
        a = hmtype.TyVar()
        ty_fn = _FunctionType([a, a], ty_bool)
        ty_scheme = hmtype.TyScheme([a], hmtype.noConstraints, ty_fn)
        gamma.add(oper, ty_scheme)

    # bit wise opers: int -> int -> int
    bitwise_opers = [
        pyon.builtin_data.oper_BITWISEAND,
        pyon.builtin_data.oper_BITWISEOR,
        pyon.builtin_data.oper_BITWISEXOR
    ]
    for oper in bitwise_opers:
        ty_fn = _FunctionType([ty_int, ty_int], ty_int)
        gamma.add(oper, ty_fn)

    # mod
    gamma.add(pyon.builtin_data.oper_MOD, _FunctionType([ty_int, ty_int], ty_int))

    # negate
    a = hmtype.TyVar()
    gamma.add(pyon.builtin_data.oper_NEGATE,
        hmtype.TyScheme([a], hmtype.noConstraints, _FunctionType([a], a)))

    # power
    a = hmtype.TyVar()
    gamma.add(pyon.builtin_data.oper_POWER, _FunctionType([a, a], a))

    # floordiv
    a = ty_int
    gamma.add(pyon.builtin_data.oper_FLOORDIV, _FunctionType([a, a], a))

    # list
    a = hmtype.TyVar()
    gamma.add(pyon.builtin_data.oper_LIST,
        hmtype.TyScheme([a], hmtype.noConstraints, 
            _FunctionType([_IterType(a)], _ListType(a))))

    # foreach
    a = hmtype.TyVar()
    b = hmtype.TyVar()
    gamma.add(pyon.builtin_data.oper_FOREACH,
        hmtype.TyScheme([a, b], hmtype.noConstraints, _ForeachType(a, b)))

    # do
    a = hmtype.TyVar()
    gamma.add(pyon.builtin_data.oper_DO,
        hmtype.TyScheme([a], hmtype.noConstraints, _FunctionType([a], _IterType(a))))

def literalSignature(c):
    tyc = c.__class__
    if tyc is bool:
        return ty_bool
    elif tyc is int:
        return ty_int
    elif tyc is float:
        return ty_float
    elif c is None:
        return ty_None
    else:
        debug("unknown literal")
        raise TypeError

def generalize(gamma, ty):
    ftv_ty = ty.freeVariables()
    ftv_gamma = gamma.freeVariables()
    qvars = ftv_ty.difference(ftv_gamma)
    if list(qvars) == []:
        return ty
    return hmtype.TyScheme(list(qvars), hmtype.noConstraints, ty)

class Gamma():
    def __init__(self, g=None):
        if g == None:
            self.env = dict()
        else:
            self.env = dict(g.env)

    def lookup(self, n):
        for var, ty in self.env.items():
            if var == n:
                return ty
        return None

    def subst(self, s):
        for tv in self.env:
            if isinstance(tv.type, hmtype.TyScheme):
                continue
            try:
                tv.type.rename(s)
            except:
                debug("Gamma.subst")

    def add(self, var, ty):
        assert isinstance(var, ast.Variable)
        assert isinstance(ty, hmtype.PyonTypeBase)
        assert var != None and ty != None
        self.env[var] = ty

    def remove(self, var):
        self.env.remove(var)

    def freeVariables(self):
        s = set()
        for ty in self.env.values():
            s.union(ty.freeVariables())
        return list(s)

    def dump(self):
        print "************************************"
        for v, ty in self.env.items():
            if v.name == None:
                print '?%d :' % v.identifier,
            else:
                print '%s%d :' % (v.name, v.identifier),
            if isinstance(ty, hmtype.TyScheme):
                ty = ty.instantiate()
                print "(scheme) ",
            print "%s" % pretty.render(ty.pretty())
        print "************************************"

def performHMTypeInference(gamma, expr):
    """implementation of Algorithm W. gamma * expr -> subst * type
    """

    if isinstance(expr, ast.Expression):
        if isinstance(expr, ast.VariableExpr):
            ty = gamma.lookup(expr.variable)
            if ty:
                if isinstance(ty, hmtype.TyScheme):
                    return ty.instantiate()
                else:
                    return ty
            else:
                raise TypeError, type(expr)

        elif isinstance(expr, ast.LiteralExpr):
            return literalSignature(expr.literal)

        elif isinstance(expr, ast.IfExpr):
            ty_cond = performHMTypeInference(gamma, expr.argument)
            expr.argument.type = unification.unify(ty_cond, ty_bool)
            expr.ifTrue.type = performHMTypeInference(gamma, expr.ifTrue)
            expr.ifFalse.type = performHMTypeInference(gamma, expr.ifFalse)
            ty = expr.type = unification.unify(expr.ifTrue.type, expr.ifFalse.type)
            return ty

        elif isinstance(expr, ast.TupleExpr):
            for arg in expr.arguments:
                arg.type = performHMTypeInference(gamma, arg)
            ty = expr.type = hmtype.TupleTy([arg.type for arg in expr.arguments])
            return ty

        elif isinstance(expr, ast.CallExpr):
            ty_oper = performHMTypeInference(gamma, expr.operator)
            for arg in expr.arguments:
                arg.type = performHMTypeInference(gamma, arg)
            ty_fn = _FunctionType(
                        [arg.type for arg in expr.arguments], hmtype.TyVar()
                        )

            for arg in expr.arguments:
              if not isinstance(ty_oper, hmtype.FunTy):
                  raise TypeError, type(expr)
              unification.unify(arg.type, ty_oper.domain)
              ty_oper = ty_oper.range
              ty_fn = ty_fn.range
            ty = unification.unify(ty_oper, ty_fn)
            expr.type = ty
            return ty

        elif isinstance(expr, ast.LetExpr):
            ty = expr.parameter.type = performHMTypeInference(gamma, expr.rhs)

            if isinstance(expr.parameter, ast.TupleParam):
                if isinstance(ty, hmtype.TyVar):
                    args = []
                    for i in range(len(expr.parameter.fields)):
                        args.append(hmtype.TyVar())
                    ty = unification.unify(hmtype.TupleTy(args), ty)
                else:
                    if len(expr.parameter.fields) != len(ty.arguments):
                        raise TypeError, type(expr)

                for i in range(len(expr.parameter.fields)):
                    ty_scheme = generalize(gamma, ty.arguments[i])
                    expr.parameter.fields[i].type = ty_scheme
                    gamma.add(expr.parameter.fields[i].name, ty_scheme)

            else:
                ty_scheme = generalize(gamma, ty)
                expr.parameter.type = ty_scheme
                gamma.add(expr.parameter.name, ty_scheme)

            ty = expr.body.type = performHMTypeInference(gamma, expr.body)
            return ty

        elif isinstance(expr, ast.LetrecExpr):
            for definition in expr.definitions:
                ty_fn = performHMTypeInference(gamma, definition.function)
                gamma.add(definition.name, ty_fn)
            ty = expr.type = performHMTypeInference(gamma, expr.body)
            return ty

        elif isinstance(expr, ast.UndefinedExpr):
            return hmtype.TyVar() 

        elif isinstance(expr, ast.FunExpr):
            if expr.function.parameters != []:
                for param in expr.function.parameters:
                    if isinstance(param, ast.TupleParam):
                        for field in param.fields:
                            field.type = hmtype.TyVar()
                            gamma.add(field.name, field.type)
                        param.type = hmtype.TupleTy([field.type for field in param.fields])
                    else:
                        param.type = hmtype.TyVar()
                        gamma.add(param.name, param.type)

                ty_domain = [param.type]
                ty_range = performHMTypeInference(gamma, expr.function.body)
                ty = expr.type = _FunctionType(ty_domain, ty_range)
                return ty
            else:
                # TODO: lambda function without arguments
                ty = expr.type = performHMTypeInference(gamma, expr.function.body)
                return ty

        else:
            debug("expr: variable: unknown")
            raise TypeError, type(expr)

    elif isinstance(expr, ast.Function):
        for param in expr.parameters:
            param.type = hmtype.TyVar()
            gamma.add(param.name, param.type)
        ty_body = performHMTypeInference(gamma, expr.body)
        ty = expr.type = _FunctionType([param.type for param in expr.parameters], ty_body)
        return ty

    elif isinstance(expr, ast.Variable):
        return gamma.lookup(expr)

    elif isinstance(expr, ast.Parameter):
        ty = expr.type = performHMTypeInference(gamma, expr.name)
        return ty 

    else:
        print "Error: unknown type of expression: %s" % expr.__class__.__name__
        raise TypeError, type(expr)

def collectFunctionDefType(global_gamma, fndef_expr):
    if isinstance(fndef_expr, ast.FunctionDef):
        local_gamma = Gamma(global_gamma)

        for p in fndef_expr.function.parameters:
            p.type = hmtype.TyVar()
            local_gamma.add(p.name, p.type)

        ty_body = performHMTypeInference(local_gamma, fndef_expr.function.body)
        ty_fn = _FunctionType(
                      [param.type for param in fndef_expr.function.parameters], ty_body
                    )
        fndef_expr.type = hmtype.TyScheme(
                  list(ty_fn.freeVariables()),
                  hmtype.noConstraints,
                  ty_fn
                )
        global_gamma.add(fndef_expr.name, fndef_expr.type)

def doTypeInference(anf_form):
    if isinstance(anf_form, ast.Module):
        global_gamma = Gamma()
        populateIntrinsicOperations(global_gamma)
        for fndef in anf_form.iterDefinitions():
            collectFunctionDefType(global_gamma, fndef)

def inferTypes(anf_form):
    doTypeInference(anf_form)


