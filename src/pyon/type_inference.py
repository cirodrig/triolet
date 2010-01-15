
import pyon.ast.ast as ast
import pyon.ast.print_ast as print_ast
import pyon
import pyon.pretty as pretty
import pyon.builtin_data as builtin_data
import pyon.unification as unification
import pyon.types.hmtype as hmtype
import pdb

class TypeCheckError(Exception): pass

def debug(msg):
    print msg
    pdb.set_trace()

def typrn(ty):
    pretty.render(ty.canonicalize().pretty())

def _functionType(param_types, return_type):
    # Affix parameter types onto the return type, starting with the last
    t = return_type
    for param_t in reversed(param_types): t = hmtype.FunTy(param_t, t)
    return t

def literalSignature(c):
    tyc = c.__class__
    if tyc is bool:
        return builtin_data.type_bool
    elif tyc is int:
        return builtin_data.type_int
    elif tyc is float:
        return builtin_data.type_float
    elif c is None:
        return builtin_data.type_None
    else:
        debug("unknown literal")
        raise TypeError

def generalize(gamma, ty):
    ftv_ty = ty.freeVariables()
    ftv_gamma = gamma.freeVariables()
    qvars = ftv_ty.difference(ftv_gamma)
    return hmtype.TyScheme(list(qvars), hmtype.noConstraints, ty)

class Gamma(object):
    def __init__(self, xs=[]):
        # Either use xs as a dictionary, or make a dictionary from it
        if type(xs) is dict: self.env = xs
        else: self.env = dict(xs)

    @classmethod
    def singleton(cls, name, ty):
        "Create an environment containing exactly one assignment"
        return cls([(name, ty)])

    @classmethod
    def union(cls, g1, g2):
        d = g1.env.copy()
        d.update(g2.env)
        return cls(d)

    @classmethod
    def unions(cls, xs):
        d = dict()
        for x in xs: d.update(x.env)
        return cls(d)

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

def inferLetBindingType(gamma, param, bound_type, expr):
    """
    Infer types in a let-binding.  Bound variables are assigned a type scheme.
    The expression 'expr' is only used for error reporting.
    """

    if isinstance(param, ast.TupleParam):
        # Unify the bound type with a tuple type
        n_fields = len(param.fields)
        field_types = [hmtype.TyVar() for _ in range(n_fields)]

        try:
            tuple_type = unification.unify(hmtype.TupleTy(field_types),
                                           bound_type)
        except unification.UnificationError, e:
            typrn(expr)
            raise TypeCheckError, "Type mismatch in parameter binding"

        # Bind each tuple field to a variable
        for p, t in zip(param.fields, field_types):
            inferLetBindingType(gamma, p, t, expr)

    elif isinstance(param, ast.VariableParam):
        # Generalize this type and assign the variable's type
        param.name.typeScheme = generalize(gamma, bound_type)

    else:
        raise TypeError, type(param)

def exposeMonoBinding(gamma, param):
    """
    exposeMonoBinding(gamma, param) -> (environment, type)
    Create new types for a monomorphic binding.
    Bound variables are returned as a new environment that is disjoint from
    the given environment.
    """

    if isinstance(param, ast.TupleParam):
        (env, field_types) = exposeMonoBindings(gamma, param.fields)
        return (env, hmtype.TupleTy(field_types))

    elif isinstance(param, ast.VariableParam):
        # Instantiate with a new type variable
        t = hmtype.TyVar()
        return (Gamma.singleton(param.name, t), t)

    else:
        raise TypeError, type(param)

def exposeMonoBindings(gamma, params):
    """
    Expose a list of bindings.
    """
    envs = []
    types = []
    for p in params:
        env, t = exposeMonoBinding(gamma, p)
        assert isinstance(env, Gamma)
        assert isinstance(t, hmtype.PyonTypeBase)
        envs.append(env)
        types.append(t)

    return (Gamma.unions(envs), types)
        

def inferFunctionType(gamma, func):
    """
    Infer and return the type of a function.  The result is a monotype.
    """
    # Create local environment
    (local_env, param_types) = exposeMonoBindings(gamma, func.parameters)
    gamma = Gamma.union(gamma, local_env)

    # Process body
    rng = inferExpressionType(gamma, func.body)

    return _functionType(param_types, rng)

def inferDefGroup(gamma, group):
    """
    Infer types in a definition group.  Each function in the group is assigned
    a type scheme.
    """
    # Add definitions to local environment
    (local_env, _) = exposeMonoBindings(gamma,
                                        (ast.VariableParam(d.name)
                                         for d in group))
    gamma = Gamma.union(gamma, local_env)

    # Infer function types
    def_types = [inferFunctionType(gamma, d.function) for d in group]

    # Generalize functions
    for d, ty in zip(group, def_types):
        d.name.typeScheme = generalize(gamma, ty)

def inferExpressionType(gamma, expr):
    """
    Infer the type of an expression in environment @gamma.
    """

    # Structural recursion.  Infer types of subexpressions and put
    # the expression's type in 'ty'
    if isinstance(expr, ast.VariableExpr):
        v = expr.variable

        # If the variable has a type scheme, then instantiate it.
        # Otherwise, look up its type in the environment.
        if v.typeScheme is not None:
            ty = v.typeScheme.instantiate()
        else:
            ty = gamma.lookup(v)
            if ty is None:
                raise IndexError, v.name

    elif isinstance(expr, ast.LiteralExpr):
        ty = literalSignature(expr.literal)

    elif isinstance(expr, ast.IfExpr):
        ty_cond = inferExpressionType(gamma, expr.argument)
        try:
            unification.unify(ty_cond, builtin_data.type_bool)
        except unification.UnificationError, e:
            print_ast.printAst(expr.argument)
            raise TypeCheckError, "Condition of 'if' expression msut be a boolean"
        ty_true = inferExpressionType(gamma, expr.ifTrue)
        ty_false = inferExpressionType(gamma, expr.ifFalse)

        try:
            ty = unification.unify(ty_true, ty_false)
        except unification.UnificationError, e:
            print_ast.printAst(expr)
            raise TypeCheckError, "Branches of 'if' expression have different types"

    elif isinstance(expr, ast.TupleExpr):
        for arg in expr.arguments:
            arg.type = inferExpressionType(gamma, arg)
        ty = hmtype.TupleTy([arg.type for arg in expr.arguments])

    elif isinstance(expr, ast.CallExpr):
        # Infer types of subexpressions
        ty_oper = inferExpressionType(gamma, expr.operator)
        ty_args = [inferExpressionType(gamma, arg) for arg in expr.arguments]

        # Create function type; unify
        ty = hmtype.TyVar()
        ty_fn = _functionType(ty_args, ty)
        try:
            unification.unify(ty_oper, ty_fn)
        except unification.UnificationError, e:
            print_ast.printAst(expr)
            print "Function type:", pretty.renderString(ty_oper.pretty())
            print "Argument types:", [pretty.renderString(x.pretty()) for x in ty_args]
            raise TypeCheckError, "Type mismatch in function call"

    elif isinstance(expr, ast.LetExpr):
        # Process the RHS
        ty_rhs = inferExpressionType(gamma, expr.rhs)

        # Bind the LHS
        inferLetBindingType(gamma, expr.parameter, ty_rhs, expr)

        # Process the body
        ty = inferExpressionType(gamma, expr.body)

    elif isinstance(expr, ast.LetrecExpr):
        # Process the local functions and assign type schemes
        inferDefGroup(gamma, expr.definitions)

        # Infer body of letrec
        ty = inferExpressionType(gamma, expr.body)

    elif isinstance(expr, ast.UndefinedExpr):
        ty = hmtype.TyVar()

    elif isinstance(expr, ast.FunExpr):
        ty = inferFunctionType(gamma, expr.function)

    else:
        debug("expr: variable: unknown")
        raise TypeError, type(expr)

    # Save and return the computed type
    assert isinstance(ty, hmtype.PyonTypeBase)
    expr.type = ty
    return ty

def doTypeInference(anf_form):
    if isinstance(anf_form, ast.Module):
        global_gamma = Gamma()
        for defgroup in anf_form.iterDefinitionGroups():
            inferDefGroup(global_gamma, defgroup)

def inferTypes(anf_form):
    doTypeInference(anf_form)


