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

import itertools
import sys

import pyon
import pyon.ast.ast as ast
import pyon.ast.print_ast as print_ast
import pyon.pretty as pretty
import pyon.builtin_data as builtin_data
import pyon.unification as unification
import pyon.types.types as hmtype

class TypeCheckError(Exception): pass

def typrn(ty):
    pretty.render(ty.canonicalize().pretty())

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

    For a given variable v, if v is in scope, then
    * self[v] is undefined, v's type was already defined before type inference
      began, and v.getTypeScheme() is the variable's type scheme, or
    * self[v] = None and v.getTypeScheme() is the variable's type scheme, or
    * self[v] = RecVarPlaceholder(v, t) where t is the variable's type
                before generalization, or
    * self[v] = t where t is the variable's first-order type.

    In the first case, a VariableExpr is replaced by a placeholder when its
    type is looked up, because creation of dictionaries is deferred.  In the
    latter two cases, a VariableExpr remains itself.
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
            if ty is None: v.getTypeScheme().addFreeVariables(s)
            elif isinstance(ty, hmtype.FirstOrderType):
                ty.addFreeVariables(s)
            elif isinstance(ty, ast.RecVarPlaceholderExpr):
                ty.getType().addFreeVariables(s)
            else:
                raise TypeError, type(ty)
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
    findVariableType(Environment, ANFVariable)
        -> (constraints, placeholders, Expression, FirstOrderType)

    Get the type of a variable and a list of class constraints.  If the
    variable has a type scheme, instantiate it.
    """
    scm = v.getTypeScheme()

    # Case 1: type scheme
    if scm:
        constraints, ty = scm.instantiate()

        # Convert to dictionary-passing form
        params = [ast.DictPlaceholderExpr(c, base = ast.ExprInit(type = c.getDictionaryType()))
                  for c in constraints]

        expr = hmtype.makeDictionaryPassingCall(v, params, ty)
        return (constraints, params, expr, ty)

    # else
    entry = env[v]

    # Case 2: placeholder
    if isinstance(entry, ast.RecVarPlaceholderExpr):
        return ([], [entry], entry, entry.getType())

    # else
    # Case 3: first-order type
    assert isinstance(entry, hmtype.FirstOrderType)
    oper = ast.VariableExpr(v, base = ast.ExprInit(type = entry))
    return ([], [], oper, entry)

def findVariableTypeScheme(env, v):
    """
    Get the type scheme of a variable, if it has been assigned one.
    Otherwise, return None.
    The variable must be in the environment.
    """
    if env[v] is None: return v.getTypeScheme()
    else: return None

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

def assumePlaceholderType(env, v, t):
    """
    assumePlaceholderType(env, v, t) -- add a placeholder to env[v]

    Create a dictionary-passing placeholder for @v, and record it in the
    environment.  The first-order type @t is assigned to @v.
    """
    assert isinstance(v, ast.ANFVariable)
    assert isinstance(t, hmtype.FirstOrderType)
    assert v not in env

    env[v] = ast.RecVarPlaceholderExpr(v, base = ast.ExprInit(type = t))

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
    # Determine which type variables to generalize over
    ftv_ty = ty.freeVariables()
    ftv_gamma = gamma.freeVariables()
    qvars = ftv_ty.difference(ftv_gamma)

    # Determine which constraints to generalize over
    (retained, deferred) = hmtype.splitConstraints(constraints,
                                                   ftv_gamma,
                                                   qvars)

    return (deferred, hmtype.TyScheme(list(qvars), retained, ty))

def generalizeGroup(gamma, constraints, ty_list):
    # Determine which type variables to generalize over
    ftv_ty = set()
    for ty in ty_list: ty.addFreeVariables(ftv_ty)
    ftv_gamma = gamma.freeVariables()
    qvars = ftv_ty.difference(ftv_gamma)

    # Determine which constraints to generalize over
    (retained, deferred) = hmtype.splitConstraints(constraints,
                                                   ftv_gamma,
                                                   qvars)

    # Create type schemes
    qvars_list = list(qvars)
    schemes = [hmtype.TyScheme(qvars_list, retained, ty) for ty in ty_list]
        
    return (deferred, retained, schemes)

def assignGeneralizedType(gamma, v, ty, constraints):
    """
    assignGeneralizedType(Environment, TyVar, FirstOrderType, constraints)
        -> (DictEnvironment, constraints)

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
    return deferred

def assignGeneralizedTypes(gamma, assignments, constraints):
    """
    assignGeneralizedTypes(Environment, sequence((TyVar, FirstOrderType)), constraints)
        -> (deferred constraints, retained constraints)

    Generalize a list of types in a common context.  All types in the list will
    have the same quantified variables and constraints.
    """
    vars = []
    types = []
    for v, ty in assignments:
        vars.append(v)
        types.append(ty)

    # Generalize with a common context
    (deferred, retained, schemes) = generalizeGroup(gamma, constraints, types)

    # Assign each type
    for v, scm in itertools.izip(vars, schemes):
        v.setTypeScheme(scm)
        gamma[v] = None
    return (deferred, retained)

###############################################################################
# Helper functions for collecting results

def combine(combiner, accumulator, sq):
    """
    combine : (b -> ()) -> a -> [(b, c)] -> (a, [c])

    Accumulate results from a sequence of calls.
    The combiner takes results and adds them to the accumulator in-place.
    The accumulator is returned.
    """
    ret = []
    for x, y in sq:
        combiner(x)
        ret.append(y)
    return (accumulator, ret)

def collectConstraints(sq):
    constraints = []
    def combiner(csts):
        constraints.extend(csts)

    return combine(combiner, constraints, sq)

def collectCPh(sq):
    constraints = []
    placeholders = []
    def combiner((csts, phs)):
        constraints.extend(csts)
        placeholders.extend(phs)

    return combine(combiner, (constraints, placeholders), sq)

###############################################################################
# Dictionary-passing translation

def makeDictionaryEnvironment(constraints):
    """
    Create a dictionary environment.  Assign a fresh variable (that stands for
    a class dictionary) to each constraint.
    """
    def mkvar(cst):
        type = cst.getDictionaryType()
        scm = hmtype.TyScheme([], hmtype.noConstraints, type)
        return ast.ANFVariable(type_scheme = scm)

    return [(c, mkvar(c)) for c in constraints]

def addDictionaryParameters(dict_env, fn_def):
    """
    Add parameters corresponding to a dictionary environment to a function
    definition.  The function definition's body is updated in-place.
    """
    dict_parameters = \
        [ast.VariableParam(v, type = v.getTypeScheme().instantiateFirstOrder())
         for _, v in dict_env]

    fn_def.function.setDictionaryParameters(dict_parameters)

def findConstraintDictionary(dict_env, constraint):
    """
    findConstraintDictionary([(ClassPredicate, ANFVariable)], ClassPredicate)
        -> (placeholders, Expression) or None
        
    Generate a dictionary for the given constraint from the dictionary
    environment.  If it can't be generated, return None.
    """
    # Get the derivation of this constraint
    derivation, hnf_predicates = constraint.toHNF()
    placeholders, expr = derivation.getCode(dict_env)

    # If the expression is a dictionary placeholder, then no progress was made
    if isinstance(expr, ast.DictPlaceholderExpr): return None

    # Otherwise, use the results
    return (placeholders, expr)

def updateDictPlaceholder(gamma, dict_env, placeholder):
    """
    Update a placeholder that represents a class dictionary.
    """
    assert isinstance(placeholder, ast.DictPlaceholderExpr)

    # Search for the dictionary in the environment
    result = findConstraintDictionary(dict_env, placeholder.getConstraint())
    if result:
        # Partly or fully resolved
        new_placeholders, dict_expr = result
        placeholder.setElaboration(dict_expr)
        return new_placeholders
    else:
        # Not resolved
        return [placeholder]

def updateRecVarPlaceholder(gamma, dict_env, placeholder):
    """
    Update a placeholder that represents a recursive variable reference.
    The placeholder either becomes a variable (if no dictionary
    parameters are required) or a function call with dictionary parameters
    (if the dictionary parameters are required).

    The placeholder is resolved, and new dictionary placeholders may be
    created.  A list of new, unresolved placeholders is returned.
    """
    assert isinstance(placeholder, ast.RecVarPlaceholderExpr)
    assert placeholder.dictionaryArguments is None

    result_type = placeholder.getType()
    variable = placeholder.getVariable()

    # The variable should have a type scheme now.  Use the type scheme to
    # determine what dictionary placeholders are.
    scm = findVariableTypeScheme(gamma, variable)
    if not scm:
        raise RuntimeError, "No type inferred for recursive variable"

    # If there are no class constraints, then instantiate it as an
    # ordinary variable.  No further work remains.
    if not len(scm.constraints):
        oper = ast.VariableExpr(variable,
                                base = ast.ExprInit(type = result_type))
        placeholder.setElaboration(oper)
        return []

    # Else, create a dictionary-passing function call.
    # Create a parameter placeholder for each dictionary constraint
    oper_constraints, oper_result_type = scm.instantiate()

    # Make the instantiated type and constraints match the expected type.
    # This must succeed, because type inference has succeeded.
    try: unification.unify(oper_result_type, result_type)
    except UnificationError, e:
        raise RuntimeError, "Dictionary elaboration failed"

    # Make dictionary parameters.  Also, resolve them.
    dict_parameters = []
    unresolved_dict_parameters = []
    dict_type_parameters = []
    for cst in oper_constraints:
        ty = cst.getDictionaryType()
        param = ast.DictPlaceholderExpr(cst, base = ast.ExprInit(type = ty))
        local_unresolved = updateDictPlaceholder(gamma, dict_env, param)

        unresolved_dict_parameters += local_unresolved
        dict_parameters.append(param)
        dict_type_parameters.append(ty)

    # Make dictionary-passing type
    oper_type = hmtype.functionType(dict_type_parameters, result_type)
    
    # Build call expression
    oper = ast.VariableExpr(variable,
                            base = ast.ExprInit(type = oper_type))
    call = ast.CallExpr(oper, dict_parameters,
                        base = ast.ExprInit(type = result_type))

    # Record resolution for this placeholder
    placeholder.setElaboration(call)

    # Return the unresolved dictionaries
    return unresolved_dict_parameters

def updateRecVarPlaceholders(gamma, dict_env, placeholders):
    """
    updateRecVarPlaceholders(gamma, DictEnvironment, placeholders)
        -> deferred placeholders

    Update the placeholders from a definition group after processing the
    definition group.  Placeholders that are deferred (because they refer to
    type variables that are not bound in the definition group) are returned.
    The environment should be that which is visible after generalization.
    """
    # Unresolved placeholders are put into this list
    deferred = []

    for ph in placeholders:
        if isinstance(ph, ast.RecVarPlaceholderExpr):
            new_phs = updateRecVarPlaceholder(gamma, dict_env, ph)
        elif isinstance(ph, ast.DictPlaceholderExpr):
            new_phs = updateDictPlaceholder(gamma, dict_env, ph)
        else:
            raise TypeError, type(ph)

        deferred.extend(new_phs)

    return deferred

###############################################################################
# Type inference

def inferLetBindingType(gamma, param, bound_constraints, bound_type, expr):
    """
    inferLetBindingType(Environment, Parameter, constraints, FirstOrderType,
                        Expression) -> (constraints, Parameter)

    Infer types in a let-binding.  Bound variables are assigned a type scheme.
    The expression 'expr' is only used for error reporting.  The types are
    added to the environment.

    Returns a list of deferred constraints, and a type-annotated parameter.
    """

    if param is None:
        # No constraints
        return (bound_constraints, None)
    elif isinstance(param, ast.TupleParam):
        # Unify the bound type with a tuple type
        field_types = [hmtype.TyVar() for _ in param.fields]

        try:
            tuple_type = unification.unify(hmtype.tupleType(field_types),
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
        csts = assignGeneralizedType(gamma, param.name, bound_type,
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
                              type = hmtype.tupleType([p.getType() for p in new_fields]))

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

def exposeRecursiveVariable(gamma, v):
    """
    exposeRecursiveVariable(gamma, v) -> first-order type

    Create new first-order types for a variable defined in a recursive
    binding group.
    The environment is updated with types and dictionary-passing placeholder
    information.
    """
    # Create a new type variable for this parameter
    t = hmtype.TyVar()
    assumePlaceholderType(gamma, v, t)
    return t

def exposeRecursiveVariables(gamma, vars):
    return [exposeRecursiveVariable(gamma, v) for v in vars]

def exposeRecursiveBinding(gamma, param):
    """
    exposeRecursiveBinding(gamma, param) -> first-order type

    Create new first-order types for a recursive binding.
    The environment is updated with types and dictionary-passing placeholder
    information.
    """
    if isinstance(param, ast.TupleParam):
        field_types = exposeRecursiveBindings(gamma, param.fields)
        return hmtype.tupleType(field_types)

    elif isinstance(param, ast.VariableParam):
        return exposeRecursiveVariable(gamma, param.name)

    else:
        raise TypeError, type(param)

def exposeRecursiveBindings(gamma, params):
    return [exposeRecursiveBinding(gamma, p) for p in params]

def inferFunctionType(gamma, func):
    """
    inferFunctionType(Environment, Function)
        -> (constraints, placeholders, Function)

    Infer the type of a function.  Return a copy of the function with type
    information attached.
    """
    # Create local environment by extending gamma with the function parameters
    local_env = Environment(gamma)
    parameters = exposeFirstOrderBindings(local_env, func.parameters)
    param_types = [p.getType() for p in parameters]

    # Process body
    (csts, placeholders), body = inferExpressionType(local_env, func.body)

    new_func = ast.Function(func.mode, parameters, body,
                            type = hmtype.functionType(param_types, body.getType()))

    return (csts, placeholders, new_func)

def inferDefGroup(gamma, group):
    """
    inferDefGroup(gamma, group)
        -> (environment, constraints, placeholders, group)

    Infer types in a definition group.  Each function in the group is assigned
    a type scheme.  The definition group's type assignments are returned as a
    new environment.
    """
    # Describe the variables bound by the definition group
    bound_vars = [d.name for d in group]
    
    # Make a local copy of the environment containing the mutually recursive
    # definitions.  The definitions are given first-order types in the local
    # environment.
    rec_gamma = Environment(gamma)

    # Add definitions to a local copy of the environment
    binding_types = exposeRecursiveVariables(rec_gamma, bound_vars)

    # Infer all function types in the definition group.
    # Return the rewritten functions.
    def inferFun(d, d_type):
        fn_csts, fn_ph, fn = inferFunctionType(rec_gamma, d.function)

        # Unify the function's assumed type with the inferred type
        try: unification.unify(fn.type, d_type)
        except unification.UnificationError, e:
            raise TypeCheckError, "Type error in recursive definition group"

        # Save the function's name and body
        new_fn = ast.FunctionDef(d.name, fn)

        return ((fn_csts, fn_ph), new_fn)

    # The functions in the definition group will have the same
    # class constraint context.
    (group_csts, group_phs), new_group = \
        collectCPh(inferFun(*x) for x in zip(group, binding_types))

    # Generalize the function types
    # Note that we generalize with the environment that will be seen in
    # subsequent code (gamma), not the local environment
    deferred_csts, retained_csts = \
        assignGeneralizedTypes(gamma,
                               zip(bound_vars, binding_types),
                               group_csts)

    # Add dictionary variable parameters to each function
    dict_env = makeDictionaryEnvironment(retained_csts)
    for f in new_group:
        addDictionaryParameters(dict_env, f)

    # Update placeholders from the old environment
    deferred_phs = updateRecVarPlaceholders(gamma, dict_env, group_phs)

    return (deferred_csts, deferred_phs, new_group)

def inferExpressionType(gamma, expr):
    """
    inferExpressionType(env, expr) -> ((constraints, placeholders), Expression)

    Infer the type of an expression in environment @env.
    Return a new copy of the expression; the returned expression's type is
    stored in its 'type' field.
    """
    assert isinstance(gamma, Environment)
    assert isinstance(expr, ast.Expression)

    # Structural recursion.  Infer types of subexpressions.
    # In each branch:
    #   put the new, typed expression in 'new_expr'
    #   put the set of constraints in 'csts'
    #   put the list of generated placeholders in 'placeholders'
    #   do not update the environment
    if isinstance(expr, ast.VariableExpr):
        # If the variable has a type scheme, then instantiate it.
        # Otherwise, look up its type in the environment.
        csts, placeholders, new_expr, ty = findVariableType(gamma,
                                                            expr.variable)

    elif isinstance(expr, ast.LiteralExpr):
        ty = literalSignature(expr.literal)
        new_expr = ast.LiteralExpr(expr.literal,
                                   base = ast.ExprInit(type = ty))
        csts = []
        placeholders = []

    elif isinstance(expr, ast.IfExpr):
        (csts_cond, ph_cond), cond = inferExpressionType(gamma, expr.argument)
        try:
            unification.unify(cond.getType(), builtin_data.type_bool)
        except unification.UnificationError, e:
            print_ast.printAst(expr.argument)
            raise TypeCheckError, "Condition of 'if' expression msut be a boolean"
        (csts_true, ph_true), if_true = inferExpressionType(gamma, expr.ifTrue)
        (csts_false, ph_false), if_false = inferExpressionType(gamma, expr.ifFalse)

        try:
            ty = unification.unify(if_true.getType(), if_false.getType())
        except unification.UnificationError, e:
            print_ast.printAst(expr)
            raise TypeCheckError, "Branches of 'if' expression have different types"

        new_expr = ast.IfExpr(cond, if_true, if_false,
                              base = ast.ExprInit(type = ty))
        csts = csts_cond + csts_true + csts_false
        placeholders = ph_cond + ph_true + ph_false

    elif isinstance(expr, ast.TupleExpr):
        # Process subexpressions
        (csts, placeholders), args = \
            collectCPh(inferExpressionType(gamma, arg)
                       for arg in expr.arguments)

        # Construct tuple type
        ty = hmtype.tupleType([arg.getType() for arg in args])
        new_expr = ast.TupleExpr(args,
                                 base = ast.ExprInit(type = ty))

    elif isinstance(expr, ast.CallExpr):
        # Infer types of subexpressions
        (csts_oper, ph_oper), oper = inferExpressionType(gamma, expr.operator)
        (csts_args, ph_args), args = \
            collectCPh(inferExpressionType(gamma, arg)
                               for arg in expr.arguments)

        # Create function type; unify
        ty = hmtype.TyVar()
        ty_fn = hmtype.functionType([a.getType() for a in args], ty)
        try: unification.unify(oper.getType(), ty_fn)
        except unification.UnificationError, e:
            print_ast.printAst(expr)
            print "Function type:", pretty.renderString(ty_oper.pretty())
            print "Argument types:", [pretty.renderString(x.pretty()) for x in ty_args]
            raise TypeCheckError, "Type mismatch in function call"

        new_expr = ast.CallExpr(oper, args,
                                base = ast.ExprInit(type = ty))
        csts = csts_oper + csts_args
        placeholders = ph_oper + ph_args

    elif isinstance(expr, ast.LetExpr):
        # Process the RHS
        (csts_rhs, ph_rhs), rhs = inferExpressionType(gamma, expr.rhs)

        # Bind the LHS
        # The deferred constraints and local environment will be used while
        # processing the body
        local_gamma = Environment(gamma)
        csts_rhs_deferred, lhs = \
            inferLetBindingType(local_gamma, expr.parameter, csts_rhs,
                                rhs.getType(), expr)

        # Process the body
        (csts_body, ph_body), body = inferExpressionType(local_gamma, expr.body)
        new_expr = ast.LetExpr(lhs, rhs, body,
                               base = ast.ExprInit(type = body.getType()))
        csts = csts_rhs_deferred + csts_body
        placeholders = ph_rhs + ph_body

    elif isinstance(expr, ast.LetrecExpr):
        # Process the local functions and assign type schemes
        local_gamma = Environment(gamma)
        csts_deferred, ph_group, def_group = \
            inferDefGroup(local_gamma, expr.definitions)

        # Infer body of letrec
        (csts_body, ph_body), body = inferExpressionType(gamma, expr.body)
        new_expr = ast.LetrecExpr(def_group, body,
                                  base = ast.ExprInit(type = body.getType()))
        csts = csts_deferred + csts_body
        placeholders = ph_group + ph_body

    elif isinstance(expr, ast.UndefinedExpr):
        new_expr = ast.UndefinedExpr(base = ast.ExprInit(type = hmtype.TyVar()))
        csts = []
        placeholders = []

    elif isinstance(expr, ast.FunExpr):
        csts, placeholders, func = inferFunctionType(gamma, expr.function)
        new_expr = ast.FunExpr(func, base = ast.ExprInit(type = func.type))

    else:
        raise TypeError, type(expr)

    # Save and return the computed type
    assert isinstance(new_expr, ast.Expression)
    for c in csts: assert isinstance(c, hmtype.ClassPredicate)
    for ph in placeholders: assert isinstance(ph, ast.PlaceholderExpr)

    return ((csts, placeholders), new_expr)

def doTypeInference(anf_form):
    assert isinstance(anf_form, ast.Module)

    global_gamma = Environment()
    new_groups = []
    for defgroup in anf_form.iterDefinitionGroups():
        csts, placeholders, new_group = \
            inferDefGroup(global_gamma, defgroup)
        assert not csts     # There should be no deferred constraints here
        # assert not placeholders # All placeholders should have been resolved
        new_groups.append(new_group)

    return ast.Module(new_groups)

def inferTypes(anf_form):
    new_ast = doTypeInference(anf_form)
    removePlaceholders(new_ast)
    return new_ast

###############################################################################
# Placeholder removal: replace placeholder expressions with their actual values

def removePlaceholders(module):
    for definition in module.iterDefinitions():
        removePlaceholdersFunctionDef(definition)

def removePlaceholdersFunctionDef(fundef):
    removePlaceholdersFunction(fundef.function)

def removePlaceholdersFunction(fun):
    fun.body = removePlaceholdersExpression(fun.body)

def removePlaceholdersExpression(expr):
    if isinstance(expr, (ast.VariableExpr, ast.LiteralExpr, ast.UndefinedExpr)):
        return expr
    elif isinstance(expr, ast.TupleExpr):
        expr.arguments = [removePlaceholdersExpression(e)
                          for e in expr.arguments]
        return expr
    elif isinstance(expr, ast.DictionaryBuildExpr):
        expr.superclasses = [removePlaceholdersExpression(e)
                             for e in expr.superclasses]
        expr.methods = [removePlaceholdersExpression(e)
                        for e in expr.methods]
        return expr
    elif isinstance(expr, ast.CallExpr):
        expr.arguments = [removePlaceholdersExpression(e)
                          for e in expr.arguments]
        expr.operator = removePlaceholdersExpression(expr.operator)
        return expr
    elif isinstance(expr, ast.IfExpr): 
        expr.argument = removePlaceholdersExpression(expr.argument)
        expr.ifTrue = removePlaceholdersExpression(expr.ifTrue)
        expr.ifFalse = removePlaceholdersExpression(expr.ifFalse)
        return expr
    elif isinstance(expr, ast.FunExpr):
        removePlaceholdersFunction(expr.function)
        return expr
    elif isinstance(expr, ast.LetExpr):
        expr.rhs = removePlaceholdersExpression(expr.rhs)
        expr.body = removePlaceholdersExpression(expr.body)
        return expr
    elif isinstance(expr, ast.LetrecExpr):
        for e in expr.definitions: removePlaceholdersFunctionDef(e)
        expr.body = removePlaceholdersExpression(expr.body)
        return expr
    elif isinstance(expr, ast.PlaceholderExpr):
        # Replace with the placeholder's actual value
        return removePlaceholdersExpression(expr.getElaboration())
    else:
        raise TypeError, type(expr)


       

