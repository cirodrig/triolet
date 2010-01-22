
import pyon.ast.ast as ast
import pyon.ast.print_ast as print_ast
import pyon
import pyon.pretty as pretty
import pyon.builtin_data as builtin_data
import pyon.unification as unification
import pyon.types.types as hmtype
import pdb

class TypeCheckError(Exception): pass

def debug(msg):
    print msg
    pdb.set_trace()

def typrn(ty):
    pretty.render(ty.canonicalize().pretty())

_functionType = hmtype.FunTy

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
    Get the type of a variable and a list of class constraints.  If the
    variable has a type scheme, instantiate it.
    """
    scm = v.getTypeScheme()
    if scm: return scm.instantiate()

    ty = env[v]
    assert isinstance(ty, hmtype.FirstOrderType)
    return ([], ty)

def assumeFirstOrderType(v, t):
    """
    Assign the first-order type @t to @v.  The assignment is recorded in
    a new environment, which is returned.
    """
    assert isinstance(v, ast.ANFVariable)
    assert isinstance(t, hmtype.FirstOrderType)
    
    return Environment.singleton(v, t)

def assignFirstOrderTypeScheme(v, ty):
    """
    Assign the type scheme @scm to @v.  The assignment is recorded globally,
    and a new environment is returned.
    """
    assert isinstance(v, ast.ANFVariable)
    assert isinstance(ty, hmtype.FirstOrderType)

    scm = hmtype.TyScheme([], hmtype.noConstraints, ty)
    v.setTypeScheme(scm)
    return (Environment.singleton(v, None), [], None)

def generalize(gamma, constraints, ty):
    ftv_ty = ty.freeVariables()
    ftv_gamma = gamma.freeVariables()
    qvars = ftv_ty.difference(ftv_gamma)
    (retained, deferred) = hmtype.splitConstraints(constraints,
                                                   ftv_gamma,
                                                   qvars)
    return (deferred, hmtype.TyScheme(list(qvars), retained, ty))

def assignGeneralizedType(gamma, v, ty, constraints):
    """
    assignGeneralizedType(Environment, TyVar, FirstOrderType, constraints)
        -> (constraints, TyScheme, None)

    Generalize the type and constraints to a type scheme.
    Assign the type scheme @scm to @v.  The assignment is recorded globally.
    A new environment and the deferred constraints are returned.
    """
    assert isinstance(v, ast.ANFVariable)
    assert isinstance(ty, hmtype.FirstOrderType)
    for c in constraints: assert isinstance(c, hmtype.ClassPredicate)

    deferred, scm = generalize(gamma, constraints, ty)
    v.setTypeScheme(scm)
    return (Environment.singleton(v, None), deferred, None)

###############################################################################
# Type operations

def collectConstraints(sq):
    """
    collectConstraints(sequence (constraints, a)) -> (constraints, [a])
    """
    constraints = []
    xs = []
    for csts, x in sq:
        for c in csts: assert isinstance(c, hmtype.ClassPredicate)
        constraints += csts
        xs.append(x)
    return (constraints, xs)

def collectEnvAndConstraints(sq):
    """
    collectEnvAndConstraints(sequence (Environment, constraints, a)
        -> (Environment, constraints, [a])
    """
    env = Environment()
    csts = []
    xs = []
    for e, c, x in sq:
        assert isinstance(e, Environment)
        for c_ in c: assert isinstance(c_, hmtype.ClassPredicate)
        env.update(e)
        csts += c
        xs.append(x)
    return (env, csts, xs)

def inferLetBindingType(gamma, param, bound_constraints, bound_type, expr):
    """
    inferLetBindingType(Environment, Parameter, constraints, FirstOrderType,
                        Expression) -> (Environment, constraints, None)

    Infer types in a let-binding.  Bound variables are assigned a type scheme.
    The expression 'expr' is only used for error reporting.

    Returns an environment, a list of deferred constraints, and None.
    """

    if isinstance(param, ast.TupleParam):
        # Unify the bound type with a tuple type
        field_types = [hmtype.TyVar() for _ in param.fields]

        try:
            tuple_type = unification.unify(hmtype.TupleTy(field_types),
                                           bound_type)
        except unification.UnificationError, e:
            print_ast.printAst(expr)
            print "Value type:", pretty.renderString(bound_type.pretty())
            raise TypeCheckError, "Type mismatch in parameter binding"

        # Bind each tuple field to a variable; return the results
        return \
            collectEnvAndConstraints(inferLetBindingType(gamma,
                                                         p,
                                                         bound_constraints,
                                                         t,
                                                         expr)
                                     for p,t in zip(param.fields, field_types))

    elif isinstance(param, ast.VariableParam):
        # Generalize this type
        return assignGeneralizedType(gamma, param.name, bound_type,
                                     bound_constraints)

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
        csts, ty = findVariableType(gamma, v)
        assert not csts
        return assignFirstOrderTypeScheme(v, ty)

    elif isinstance(param, ast.TupleParam):
        return collectEnvAndConstraints(recordFirstOrderBindingTypes(gamma, f)
                                        for f in param.fields)

    else:
        raise TypeError, type(param)

def inferFunctionType(gamma, func):
    """
    inferFunctionType(Environment, Function) -> (constraints, FirstOrderType)

    Infer and return the type of a function.  The result is a first-order type.
    """
    # Create local environment
    (local_env, param_types) = exposeFirstOrderBindings(gamma, func.parameters)
    gamma = Environment.union(gamma, local_env)

    # Process body
    csts, rng = inferExpressionType(gamma, func.body)

    return (csts, _functionType(param_types, rng))

def inferDefGroup(gamma, group):
    """
    inferDefGroup(gamma, group) -> (environment, constraints, None)

    Infer types in a definition group.  Each function in the group is assigned
    a type scheme.  The definition group's type assignments are returned as a
    new environment.
    """
    # Describe the variables bound by the definition group
    bindings = [ast.VariableParam(d.name) for d in group]
    
    # Add definitions to local environment
    (local_env, _) = exposeFirstOrderBindings(gamma, bindings)
    local_gamma = Environment.union(gamma, local_env)
    csts, binding_types = \
        collectConstraints(findVariableType(local_gamma, d.name)
                           for d in group)

    # These are first-order variable bindings, and therefore shouldn't have
    # any constraints in the recursive part of the code
    assert not csts
    del csts

    # Infer all function types in the definition group.
    def inferFun(d, d_type):
        fn_csts, fn_type = inferFunctionType(local_gamma, d.function)

        # Unify the function's assumed type with the inferred type
        try: unification.unify(fn_type, d_type)
        except UnificationError, e:
            raise TypeCheckError, "Type error in recursive definition group"

        return (fn_csts, fn_type)

    # The functions in the definition group will have the same
    # class constraint context.
    group_csts, _ = collectConstraints(inferFun(*x)
                                       for x in zip(group, binding_types))

    # Generalize the function types
    # Note that we generalize with the environment that will be seen in
    # subsequent code (gamma), not the local environment
    return \
        collectEnvAndConstraints(assignGeneralizedType(gamma,
                                                       d.name,
                                                       d_type,
                                                       group_csts)
                                 for d, d_type in zip(group, binding_types))

def inferExpressionType(gamma, expr):
    """
    inferExpressionType(env, expr) -> (constraints, FirstOrderType)

    Infer the type of an expression in environment @env.
    """
    assert isinstance(gamma, Environment)
    assert isinstance(expr, ast.Expression)

    # Structural recursion.  Infer types of subexpressions.
    # Put the expression's type in 'ty' and the set of constraints in 'csts'.
    # The constraints of subexpressions are concatenated, except where
    # type generalization occurs.
    if isinstance(expr, ast.VariableExpr):
        # If the variable has a type scheme, then instantiate it.
        # Otherwise, look up its type in the environment.
        csts, ty = findVariableType(gamma, expr.variable)

    elif isinstance(expr, ast.LiteralExpr):
        ty = literalSignature(expr.literal)
        csts = []

    elif isinstance(expr, ast.IfExpr):
        csts_cond, ty_cond = inferExpressionType(gamma, expr.argument)
        try:
            unification.unify(ty_cond, builtin_data.type_bool)
        except unification.UnificationError, e:
            print_ast.printAst(expr.argument)
            raise TypeCheckError, "Condition of 'if' expression msut be a boolean"
        csts_true, ty_true = inferExpressionType(gamma, expr.ifTrue)
        csts_false, ty_false = inferExpressionType(gamma, expr.ifFalse)

        try:
            ty = unification.unify(ty_true, ty_false)
        except unification.UnificationError, e:
            print_ast.printAst(expr)
            raise TypeCheckError, "Branches of 'if' expression have different types"

        csts = csts_cond + csts_true + csts_false

    elif isinstance(expr, ast.TupleExpr):
        # Process subexpressions
        (csts, arg_types) = collectConstraints(inferExpressionType(gamma, arg)
                                               for arg in expr.arguments)

        # Construct tuple type
        ty = hmtype.TupleTy(arg_types)

    elif isinstance(expr, ast.CallExpr):
        # Infer types of subexpressions
        csts_oper, ty_oper = inferExpressionType(gamma, expr.operator)
        (csts_args, ty_args) = \
            collectConstraints(inferExpressionType(gamma, arg)
                               for arg in expr.arguments)
        csts = csts_oper + csts_args

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
        csts_rhs, ty_rhs = inferExpressionType(gamma, expr.rhs)

        # Bind the LHS
        # The deferred constraints and local environment will be used while
        # processing the body
        local_env, csts_rhs_deferred, _ = \
            inferLetBindingType(gamma, expr.parameter, csts_rhs, ty_rhs, expr)
        gamma = Environment.union(gamma, local_env)

        # Process the body
        csts_body, ty = inferExpressionType(gamma, expr.body)
        csts = csts_rhs_deferred + csts_body

    elif isinstance(expr, ast.LetrecExpr):
        # Process the local functions and assign type schemes
        local_env, csts_deferred, _ = inferDefGroup(gamma, expr.definitions)
        gamma = Environment.union(gamma, local_env)

        # Infer body of letrec
        csts_body, ty = inferExpressionType(gamma, expr.body)
        csts = csts_deferred + csts_body

    elif isinstance(expr, ast.UndefinedExpr):
        ty = hmtype.TyVar()
        csts = []

    elif isinstance(expr, ast.FunExpr):
        csts, ty = inferFunctionType(gamma, expr.function)

    else:
        debug("expr: variable: unknown")
        raise TypeError, type(expr)

    # Save and return the computed type
    assert isinstance(ty, hmtype.FirstOrderType)
    for c in csts: assert isinstance(c, hmtype.ClassPredicate)
    expr.type = ty
    return (csts, ty)

def doTypeInference(anf_form):
    if isinstance(anf_form, ast.Module):
        global_gamma = Environment()
        for defgroup in anf_form.iterDefinitionGroups():
            new_env, csts, _ = inferDefGroup(global_gamma, defgroup)
            assert not csts     # There should be no deferred constraints here
            global_gamma = Environment.union(global_gamma, new_env)

def inferTypes(anf_form):
    doTypeInference(anf_form)


