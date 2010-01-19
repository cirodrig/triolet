
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

# Mapping from a Python literal type to the corresponding Pyon type constructor
_literalSignatureTable = {
    bool       : builtin_data.type_bool,
    int        : builtin_data.type_int,
    float      : builtin_data.type_float,
    type(None) : builtin_data.type_None
    }

def literalSignature(c):
    """
    Get the type of a literal value.
    """
    try: return _literalSignatureTable[type(c)]
    except IndexError:
        debug("unknown literal")
        raise TypeError

###############################################################################
# Environments and type updates

class Environment(dict):
    """
    A type environment, which is a finite map from variables to types or
    type schemes.

    For a given variable v, if v is in scope, then either
    * self[v] = None and v.getTypeScheme() is the variable's type scheme, or
    * self[v] = t where t is the variable's first-order type.
    """
    @classmethod
    def singleton(cls, name, ty):
        """
        Environment.singleton(name, ty) -> new environment
        Create an environment containing exactly one assignment
        """
        return cls([(name, ty)])

    @classmethod
    def union(cls, g1, g2):
        """
        Environment.union(x, y) -> union of x and y
        Create the union of two environments
        """
        d = Environment(g1)
        d.update(g2)
        return d

    @classmethod
    def unions(cls, xs):
        """
        Environment.unions(seq) -> union of elements of seq
        Create tue union of all environments in a sequence
        """
        d = Environment()
        for x in xs: d.update(x)
        return d

    def freeVariables(self):
        """
        env.freeVariables() -> set

        Get the set of all free type variables mentioned in the environment
        """
        s = set()

        # Add the free type variables of each local binding to the set
        for v, ty in self.iteritems():
            if ty: ty.addFreeVariables(s)
            else: v.getTypeScheme().addFreeVariables(s)
        return s

    def dump(self):
        print "************************************"
        for v, ty in self.iteritems():
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

    ty = env[v]
    assert isinstance(ty, hmtype.FirstOrderType)
    return ty

def assumeFirstOrderType(v, t):
    """
    Assign the first-order type @t to @v.  The assignment is recorded in
    a new environment, which is returned.
    """
    assert isinstance(v, ast.ANFVariable)
    assert isinstance(t, hmtype.FirstOrderType)
    
    return Environment.singleton(v, t)

def assignTypeScheme(v, scm):
    """
    Assign the type scheme @scm to @v.  The assignment is recorded globally,
    and a new environment is returned.
    """
    assert isinstance(v, ast.ANFVariable)
    assert isinstance(scm, hmtype.TyScheme)

    v.setTypeScheme(scm)
    return Environment.singleton(v, None)

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
        local_env = Environment()
        for p, t in zip(param.fields, field_types):
            e = inferLetBindingType(gamma, p, t, expr)
            local_env.update(e)

        # Return the new environment
        return local_env

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
    local_env = Environment()
    types = []
    for p in params:
        env, t = exposeFirstOrderBinding(gamma, p)
        assert isinstance(env, Environment)
        assert isinstance(t, hmtype.FirstOrderType)
        local_env.update(env)
        types.append(t)

    return (local_env, types)

def recordFirstOrderBindingType(gamma, param):
    """
    Assign a first-order type scheme to each variable bound by 'param'.
    The type is looked up in the environment.
    A new environment fragment is returned.
    """
    if isinstance(param, ast.VariableParam):
        v = param.name
        ty = findVariableType(gamma, v)
        scm = hmtype.TyScheme([], hmtype.noConstraints, ty)
        return assignTypeScheme(v, scm)

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
    return Environment.unions(recordFirstOrderBindingTypes(gamma, p) for p in params)

def inferFunctionType(gamma, func):
    """
    Infer and return the type of a function.  The result is a first-order type.
    """
    # Create local environment
    (local_env, param_types) = exposeFirstOrderBindings(gamma, func.parameters)
    gamma = Environment.union(gamma, local_env)

    # Process body
    rng = inferExpressionType(gamma, func.body)

    return _functionType(param_types, rng)

def inferDefGroup(gamma, group):
    """
    inferDefGroup(gamma, group) -> new environment

    Infer types in a definition group.  Each function in the group is assigned
    a type scheme.  The definition group's type assignments are returned as a
    new environment.
    """
    # Describe the variables bound by the definition group
    bindings = [ast.VariableParam(d.name) for d in group]
    
    # Add definitions to local environment
    (local_env, _) = exposeFirstOrderBindings(gamma, bindings)
    local_gamma = Environment.union(gamma, local_env)
    binding_types = [findVariableType(local_gamma, d.name) for d in group]

    # Infer all function types
    for d, d_type in zip(group, binding_types):
        fn_type = inferFunctionType(local_gamma, d.function)

        # Unify the function's assumed type with the inferred type
        try: unification.unify(fn_type, d_type)
        except UnificationError, e:
            raise TypeCheckError, "Type error in recursive definition group"

    # Generalize the function types
    # Note that we generalize with the environment that will be seen in
    # subsequent code (gamma), not the local environment
    body_env = Environment()
    for d, d_type in zip(group, binding_types):
        e = assignTypeScheme(d.name, generalize(gamma, d_type))
        body_env.update(e)

    return body_env

def inferExpressionType(gamma, expr):
    """
    inferExpressionType(env, expr) -> first-order type

    Infer the type of an expression in environment @env.
    """
    assert isinstance(gamma, Environment)
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
        gamma = Environment.union(gamma, local_env)

        # Process the body
        ty = inferExpressionType(gamma, expr.body)

    elif isinstance(expr, ast.LetrecExpr):
        # Process the local functions and assign type schemes
        local_env = inferDefGroup(gamma, expr.definitions)
        gamma = Environment.union(gamma, local_env)

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
        global_gamma = Environment()
        for defgroup in anf_form.iterDefinitionGroups():
            new_env = inferDefGroup(global_gamma, defgroup)
            global_gamma = Environment.union(global_gamma, new_env)

def inferTypes(anf_form):
    doTypeInference(anf_form)


