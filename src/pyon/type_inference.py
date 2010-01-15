
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
    """
    _functionType([p1, p2 ... pN], r) -> FirstOrderType "p1 -> p2 ... pN -> r"
    """
    # Affix parameter types onto the return type, starting with the last
    t = return_type
    for param_t in reversed(param_types): t = hmtype.FunTy(param_t, t)
    return t

def literalSignature(c):
    """
    Get the type of a literal value.
    """
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

###############################################################################
# Environments and type updates

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

    def lookup(self, var):
        ty = self.env[var]
        assert isinstance(ty, hmtype.FirstOrderType)
        return ty

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
        assert isinstance(ty, hmtype.FirstOrderType)
        assert var != None and ty != None
        self.env[var] = ty

    def remove(self, var):
        self.env.remove(var)

    def freeVariables(self):
        s = set()
        for v, ty in self.env.iteritems():
            if ty: s.update(ty.freeVariables())
            else: s.update(v.getTypeScheme().freeVariables())
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

def findVariableType(env, v):
    """
    Get the type of a variable.  If the variable has a type scheme,
    instantiate it.
    """
    scm = v.getTypeScheme()
    if scm: return scm.instantiate()

    ty = env.lookup(v)
    assert isinstance(ty, hmtype.FirstOrderType)
    return ty

def assumeFirstOrderType(v, t):
    """
    Create a new type variable representing the type of 'v'.
    Return an environment with this type assignment.
    """
    assert isinstance(v, ast.ANFVariable)
    
    return Gamma.singleton(v, t)

def assignTypeScheme(v, scm):
    """
    Assign the type scheme of a variable.
    Return an environment with this type assignment.
    """
    assert isinstance(v, ast.ANFVariable)

    v.setTypeScheme(scm)
    return Gamma.singleton(v, None)

###############################################################################
# Type operations

def generalize(gamma, ty):
    ftv_ty = ty.freeVariables()
    ftv_gamma = gamma.freeVariables()
    qvars = ftv_ty.difference(ftv_gamma)
    return hmtype.TyScheme(list(qvars), hmtype.noConstraints, ty)

def inferLetBindingType(gamma, param, bound_type, expr):
    """
    Infer types in a let-binding.  Bound variables are assigned a type scheme.
    The expression 'expr' is only used for error reporting.
    """

    if isinstance(param, ast.TupleParam):
        # Unify the bound type with a tuple type
        field_types = [hmtype.TyVar() for _ in param.fields]

        try:
            tuple_type = unification.unify(hmtype.TupleTy(field_types),
                                           bound_type)
        except unification.UnificationError, e:
            print_ast.printAst(expr)
            raise TypeCheckError, "Type mismatch in parameter binding"

        # Bind each tuple field to a variable
        envs = []
        for p, t in zip(param.fields, field_types):
            e = inferLetBindingType(gamma, p, t, expr)
            envs.append(e)

        # Return the new environment
        return Gamma.unions(envs)

    elif isinstance(param, ast.VariableParam):
        # Generalize this type and assign the variable's type
        return assignTypeScheme(param.name, generalize(gamma, bound_type))

    else:
        raise TypeError, type(param)

def exposeFirstOrderBinding(gamma, param):
    """
    exposeFirstOrderBinding(gamma, param) -> (environment, type)
    Create new types for a first-order binding.
    Bound variables are returned as a new environment that is disjoint from
    the given environment.
    """

    if isinstance(param, ast.TupleParam):
        (env, field_types) = exposeFirstOrderBindings(gamma, param.fields)
        return (env, hmtype.TupleTy(field_types))

    elif isinstance(param, ast.VariableParam):
        # Create a new type variable for this parameter
        t = hmtype.TyVar()
        return (assumeFirstOrderType(param.name, t), t)

    else:
        raise TypeError, type(param)

def exposeFirstOrderBindings(gamma, params):
    """
    Expose a list of bindings.
    """
    envs = []
    types = []
    for p in params:
        env, t = exposeFirstOrderBinding(gamma, p)
        assert isinstance(env, Gamma)
        assert isinstance(t, hmtype.FirstOrderType)
        envs.append(env)
        types.append(t)

    return (Gamma.unions(envs), types)

def recordFirstOrderBindingType(gamma, param):
    """
    Assign a first-order type scheme to each variable bound by 'param'.
    The type is looked up in the environment.
    A new environment fragment is returned.
    """
    if isinstance(param, ast.VariableParam):
        v = param.name
        ty = gamma.lookup(v)
        return assignTypeScheme(v, hmtype.TyScheme([], hmtype.noConstraints, ty))
    elif isinstance(param, ast.TupleParam):
        return recordFirstOrderBindingTypes(gamma, param.fields)
    else:
        raise TypeError, type(param)

def recordFirstOrderBindingTypes(gamma, params):
    """
    Assign each variable bound by 'params' a first-order type scheme.
    The type is looked up in the environment.
    """
    # Process each binder in the list.
    # Return the union of the generated environments.
    return Gamma.unions(recordFirstOrderBindingTypes(gamma, p) for p in params)

def inferFunctionType(gamma, func):
    """
    Infer and return the type of a function.  The result is a first-order type.
    """
    # Create local environment
    (local_env, param_types) = exposeFirstOrderBindings(gamma, func.parameters)
    gamma = Gamma.union(gamma, local_env)

    # Process body
    rng = inferExpressionType(gamma, func.body)

    return _functionType(param_types, rng)

def inferDefGroup(gamma, group):
    """
    inferDefGroup(gamma, group) -> new environment
    
    Infer types in a definition group.  Each function in the group is assigned
    a type scheme.
    """
    # Describe the variables bound by the definition group
    bindings = [ast.VariableParam(d.name) for d in group]
    
    # Add definitions to local environment
    (local_env, _) = exposeFirstOrderBindings(gamma, bindings)
    local_gamma = Gamma.union(gamma, local_env)

    # Infer function types
    for d in group:
        fn_type = inferFunctionType(local_gamma, d.function)

        # Unify the function's assumed type with the inferred type
        try: unification.unify(fn_type, local_gamma.lookup(d.name))
        except UnificationError, e:
            raise TypeCheckError, "Type error in recursive definition group"

    # Generalize the function types
    # Note that we generalize with the environment that will be seen in
    # subsequent code (gamma), not the local environment
    envs = []
    for d in group:
        ty = local_gamma.lookup(d.name)
        e = assignTypeScheme(d.name, generalize(gamma, ty))
        envs.append(e)

    return Gamma.unions(envs)

def inferExpressionType(gamma, expr):
    """
    Infer the type of an expression in environment @gamma.
    """
    assert isinstance(gamma, Gamma)
    assert isinstance(expr, ast.Expression)

    # Structural recursion.  Infer types of subexpressions and put
    # the expression's type in 'ty'
    if isinstance(expr, ast.VariableExpr):
        v = expr.variable

        # If the variable has a type scheme, then instantiate it.
        # Otherwise, look up its type in the environment.
        ty = findVariableType(gamma, v)

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
        try: unification.unify(ty_oper, ty_fn)
        except unification.UnificationError, e:
            print_ast.printAst(expr)
            print "Function type:", pretty.renderString(ty_oper.pretty())
            print "Argument types:", [pretty.renderString(x.pretty()) for x in ty_args]
            raise TypeCheckError, "Type mismatch in function call"

    elif isinstance(expr, ast.LetExpr):
        # Process the RHS
        ty_rhs = inferExpressionType(gamma, expr.rhs)

        # Bind the LHS
        local_env = inferLetBindingType(gamma, expr.parameter, ty_rhs, expr)
        gamma = Gamma.union(gamma, local_env)

        # Process the body
        ty = inferExpressionType(gamma, expr.body)

    elif isinstance(expr, ast.LetrecExpr):
        # Process the local functions and assign type schemes
        local_env = inferDefGroup(gamma, expr.definitions)
        gamma = Gamma.union(gamma, local_env)

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
    assert isinstance(ty, hmtype.FirstOrderType)
    expr.type = ty
    return ty

def doTypeInference(anf_form):
    if isinstance(anf_form, ast.Module):
        global_gamma = Gamma()
        for defgroup in anf_form.iterDefinitionGroups():
            new_env = inferDefGroup(global_gamma, defgroup)
            global_gamma = Gamma.union(global_gamma, new_env)

def inferTypes(anf_form):
    doTypeInference(anf_form)


