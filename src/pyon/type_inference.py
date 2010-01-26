"""
Implementation of Hindley-Milner type inference with type classes.

Side effects:

Many functions in the module add bindings to the environment (which they take
as a parameter).  Environments are private to the module.  If a function does
not want its callee to modify the environment, it should pass a copy of the
environment.

Type inference assigns the type schemes of variables.  Type inference does not
modify modules (or their contents such as expressions).  Type inference
returns a new module that is annotated with side effect information.
"""
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

def assumeFirstOrderType(env, v, t):
    """
    assumeFirstOrderType(env, v, t) -- add the assignment v |-> t to env

    Assign the first-order type @t to @v in env.
    """
    assert isinstance(v, ast.ANFVariable)
    assert isinstance(t, hmtype.FirstOrderType)
    assert v not in env

    env[v] = t

    return None

def assignFirstOrderTypeScheme(env, v, ty):
    """
    Assign the type scheme @scm to @v.  The assignment is recorded globally
    and in the given environment.
    """
    assert isinstance(v, ast.ANFVariable)
    assert isinstance(ty, hmtype.FirstOrderType)
    assert v not in env

    scm = hmtype.TyScheme([], hmtype.noConstraints, ty)
    v.setTypeScheme(scm)
    env[v] = None

    return ([], None)

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
        -> (constraints, None)

    Generalize the type and constraints to a type scheme.
    Assign the type scheme @scm to @v.  The assignment is recorded globally.
    A new environment and the deferred constraints are returned.
    """
    assert isinstance(v, ast.ANFVariable)
    assert isinstance(ty, hmtype.FirstOrderType)
    for c in constraints: assert isinstance(c, hmtype.ClassPredicate)
    assert v not in gamma

    deferred, scm = generalize(gamma, constraints, ty)
    v.setTypeScheme(scm)
    gamma[v] = None
    return (deferred, None)

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
                        Expression) -> (constraints, Parameter)

    Infer types in a let-binding.  Bound variables are assigned a type scheme.
    The expression 'expr' is only used for error reporting.  The types are
    added to the environment.

    Returns a list of deferred constraints, and a type-annotated parameter.
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
        csts, new_params = \
            collectConstraints(inferLetBindingType(gamma,
                                                   p,
                                                   bound_constraints,
                                                   t,
                                                   expr)
                               for p,t in zip(param.fields, field_types))

        return (csts, ast.TupleParam(new_params))

    elif isinstance(param, ast.VariableParam):
        # Generalize this type
        csts, _ = assignGeneralizedType(gamma, param.name, bound_type,
                                        bound_constraints)
        return (csts, ast.VariableParam(param.name))

    else:
        raise TypeError, type(param)

def exposeFirstOrderBinding(gamma, param):
    """
    exposeFirstOrderBinding(gamma, param) -> parameter
    Create new types for a first-order binding.
    The environment is updated with type assumptions for bound variables.
    The parameter, with type attached, is returned.
    """

    if isinstance(param, ast.TupleParam):
        new_fields = exposeFirstOrderBindings(gamma, param.fields)
        return ast.TupleParam(new_fields,
                              type = hmtype.TupleTy([p.getType() for p in new_fields]))

    elif isinstance(param, ast.VariableParam):
        # Create a new type variable for this parameter
        t = hmtype.TyVar()
        assumeFirstOrderType(gamma, param.name, t)
        return ast.VariableParam(param.name, type = t)

    else:
        raise TypeError, type(param)

def exposeFirstOrderBindings(gamma, params):
    """
    Expose a list of bindings.  The environment is updated with all bindings.
    A new set of parameters, labeled with types, is returned.
    """
    # Expose bindings, updating the environment
    return [exposeFirstOrderBinding(gamma, p) for p in params]

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
        return collectConstraints(recordFirstOrderBindingTypes(gamma, f)
                                  for f in param.fields)

    else:
        raise TypeError, type(param)

def inferFunctionType(gamma, func):
    """
    inferFunctionType(Environment, Function) -> (constraints, Function)

    Infer the type of a function.  Return a copy of the function with type
    information attached.
    """
    # Create local environment by extending gamma with the function parameters
    local_env = Environment(gamma)
    parameters = exposeFirstOrderBindings(local_env, func.parameters)
    param_types = [p.getType() for p in parameters]

    # Process body
    csts, body = inferExpressionType(local_env, func.body)

    new_func = ast.Function(func.mode, parameters, body,
                            _functionType(param_types, body.getType()))

    return (csts, new_func)

def inferDefGroup(gamma, group):
    """
    inferDefGroup(gamma, group) -> (environment, constraints, group)

    Infer types in a definition group.  Each function in the group is assigned
    a type scheme.  The definition group's type assignments are returned as a
    new environment.
    """
    # Describe the variables bound by the definition group
    bindings = [ast.VariableParam(d.name) for d in group]
    
    # Make a local copy of the environment containing the mutually recursive
    # definitions.  The definitions are given first-order types in the local
    # environment.
    rec_gamma = Environment(gamma)

    # Add definitions to a local copy of the environment
    exposeFirstOrderBindings(rec_gamma, bindings)
    csts, binding_types = \
        collectConstraints(findVariableType(rec_gamma, d.name) for d in group)

    # These are first-order variable bindings, and therefore shouldn't have
    # any constraints in the recursive part of the code
    assert not csts
    del csts

    # Infer all function types in the definition group.
    # Return the rewritten functions.
    def inferFun(d, d_type):
        fn_csts, fn = inferFunctionType(rec_gamma, d.function)

        # Unify the function's assumed type with the inferred type
        try: unification.unify(fn.type, d_type)
        except unification.UnificationError, e:
            raise TypeCheckError, "Type error in recursive definition group"

        # Rebuild the function
        new_fn = ast.FunctionDef(d.name, fn)

        return (fn_csts, new_fn)

    # The functions in the definition group will have the same
    # class constraint context.
    group_csts, new_group = \
        collectConstraints(inferFun(*x) for x in zip(group, binding_types))

    # Generalize the function types
    # Note that we generalize with the environment that will be seen in
    # subsequent code (gamma), not the local environment
    deferred_csts, _ = \
        collectConstraints(assignGeneralizedType(gamma,
                                                 d.name,
                                                 d_type,
                                                 group_csts)
                           for d, d_type in zip(group, binding_types))

    return (deferred_csts, new_group)

def inferExpressionType(gamma, expr):
    """
    inferExpressionType(env, expr) -> (constraints, Expression)

    Infer the type of an expression in environment @env.
    Return a new copy of the expression; the returned expression's type is
    stored in its 'type' field.
    """
    assert isinstance(gamma, Environment)
    assert isinstance(expr, ast.Expression)

    # Structural recursion.  Infer types of subexpressions.
    # Put the new, typed expression in 'new_expr' and the set of constraints
    # in 'csts'.
    # The constraints of subexpressions are concatenated, except where
    # type generalization occurs.
    if isinstance(expr, ast.VariableExpr):
        # If the variable has a type scheme, then instantiate it.
        # Otherwise, look up its type in the environment.
        csts, ty = findVariableType(gamma, expr.variable)
        new_expr = ast.VariableExpr(expr.variable,
                                    base = ast.ExprInit(type = ty))

    elif isinstance(expr, ast.LiteralExpr):
        ty = literalSignature(expr.literal)
        new_expr = ast.LiteralExpr(expr.literal,
                                   base = ast.ExprInit(type = ty))
        csts = []

    elif isinstance(expr, ast.IfExpr):
        csts_cond, cond = inferExpressionType(gamma, expr.argument)
        try:
            unification.unify(cond.getType(), builtin_data.type_bool)
        except unification.UnificationError, e:
            print_ast.printAst(expr.argument)
            raise TypeCheckError, "Condition of 'if' expression msut be a boolean"
        csts_true, if_true = inferExpressionType(gamma, expr.ifTrue)
        csts_false, if_false = inferExpressionType(gamma, expr.ifFalse)

        try:
            ty = unification.unify(if_true.getType(), if_false.getType())
        except unification.UnificationError, e:
            print_ast.printAst(expr)
            raise TypeCheckError, "Branches of 'if' expression have different types"

        new_expr = ast.IfExpr(cond, if_true, if_false,
                              base = ast.ExprInit(type = ty))
        csts = csts_cond + csts_true + csts_false

    elif isinstance(expr, ast.TupleExpr):
        # Process subexpressions
        (csts, args) = collectConstraints(inferExpressionType(gamma, arg)
                                          for arg in expr.arguments)

        # Construct tuple type
        ty = hmtype.TupleTy([arg.getType() for arg in args])
        new_expr = ast.TupleExpr(args,
                                 base = ast.ExprInit(type = ty))

    elif isinstance(expr, ast.CallExpr):
        # Infer types of subexpressions
        csts_oper, oper = inferExpressionType(gamma, expr.operator)
        (csts_args, args) = \
            collectConstraints(inferExpressionType(gamma, arg)
                               for arg in expr.arguments)

        # Create function type; unify
        ty = hmtype.TyVar()
        ty_fn = _functionType([a.getType() for a in args], ty)
        try: unification.unify(oper.getType(), ty_fn)
        except unification.UnificationError, e:
            print_ast.printAst(expr)
            print "Function type:", pretty.renderString(ty_oper.pretty())
            print "Argument types:", [pretty.renderString(x.pretty()) for x in ty_args]
            raise TypeCheckError, "Type mismatch in function call"

        new_expr = ast.CallExpr(oper, args,
                                base = ast.ExprInit(type = ty))
        csts = csts_oper + csts_args

    elif isinstance(expr, ast.LetExpr):
        # Process the RHS
        csts_rhs, rhs = inferExpressionType(gamma, expr.rhs)

        # Bind the LHS
        # The deferred constraints and local environment will be used while
        # processing the body
        local_gamma = Environment(gamma)
        csts_rhs_deferred, lhs = \
            inferLetBindingType(local_gamma, expr.parameter, csts_rhs,
                                rhs.getType(), expr)

        # Process the body
        csts_body, body = inferExpressionType(local_gamma, expr.body)
        new_expr = ast.LetExpr(lhs, rhs, body,
                               base = ast.ExprInit(type = body.getType()))
        csts = csts_rhs_deferred + csts_body

    elif isinstance(expr, ast.LetrecExpr):
        # Process the local functions and assign type schemes
        local_gamma = Environment(gamma)
        csts_deferred, def_group = \
            inferDefGroup(local_gamma, expr.definitions)

        # Infer body of letrec
        csts_body, body = inferExpressionType(gamma, expr.body)
        new_expr = ast.LetrecExpr(def_group, body,
                                  base = ast.ExprInit(type = body.getType()))
        csts = csts_deferred + csts_body

    elif isinstance(expr, ast.UndefinedExpr):
        new_expr = ast.UndefinedExpr(base = ast.ExprInit(type = hmtype.TyVar()))
        csts = []

    elif isinstance(expr, ast.FunExpr):
        csts, func = inferFunctionType(gamma, expr.function)
        new_expr = ast.FunExpr(func, base = ast.ExprInit(type = func.type))

    else:
        debug("expr: variable: unknown")
        raise TypeError, type(expr)

    # Save and return the computed type
    assert isinstance(new_expr, ast.Expression)
    for c in csts: assert isinstance(c, hmtype.ClassPredicate)
    return (csts, new_expr)

def doTypeInference(anf_form):
    assert isinstance(anf_form, ast.Module)

    global_gamma = Environment()
    new_groups = []
    for defgroup in anf_form.iterDefinitionGroups():
        csts, new_group = \
            inferDefGroup(global_gamma, defgroup)
        assert not csts     # There should be no deferred constraints here
        new_groups.append(new_group)

    return ast.Module(new_groups)

def inferTypes(anf_form):
    return doTypeInference(anf_form)


