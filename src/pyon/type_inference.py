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
import system_f as sf
import pyon.ast.print_ast as print_ast
import pyon.pretty as pretty
import pyon.builtin_data as builtin_data
import pyon.unification as unification
import pyon.types.kind as kind
import pyon.types.types as hmtype
import pyon.types.gluon_types as gluon_types
from pyon.types.type_assignment import \
    TypeAssignment, \
    FirstOrderAssignment, PolymorphicAssignment, RecursiveAssignment
from pyon.types.placeholders import \
    RecVarPlaceholder, DictPlaceholder, IdDerivation, InstanceDerivation

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
    A type environment.  The environment maps variables to types or
    type schemes.

    For a given variable v, if v is in scope, then
    * self[v] is undefined, v's type was already defined before type inference
      began, and v.getSystemFTranslation() is the variable's type
      information, or
    * self[v] is the variable's type information.
    """
    @classmethod
    def singleton(cls, name, information):
        """
        Environment.singleton(name, information) -> new environment
        Create an environment containing exactly one assignment.
        """
        assert isinstance(information, TypeAssignment)
        return cls([(name, information)])

    @classmethod
    def union(cls, g1, g2):
        """
        Environment.union(x, y) -> union of x and y
        Create the union of two environments.
        """
        d = Environment(g1)
        d.update(g2)
        return d

    @classmethod
    def unions(cls, xs):
        """
        Environment.unions(seq) -> union of elements of seq
        Create the union of all environments in a sequence.
        """
        d = Environment()
        for x in xs: d.update(x)
        return d

    def freeVariables(self):
        """
        env.freeVariables() -> FreeVariableSet

        Get the set of all free type variables mentioned in the environment
        """
        s = hmtype.FreeVariableSet()

        # Add the free type variables of each local binding to the set
        for v, assignment in self.iteritems():
            assignment.getFreeTypeVariables(s)

        return s

    def printKeys(self):
        print "Dictionary contains:"
        for v in self:
            print " ", print_ast.printAstString(v)

def instantiateVariable(env, v):
    """
    instantiateVariable(Environment, ANFVariable)
        -> ((constraints, placeholders), (sf.Exp, FirstOrderType))

    Create the System F code representing a reference to a variable.
    """
    assert isinstance(env, Environment)
    return (v.getSystemFTranslation() or env[v]).instantiate()

def findVariableTypeScheme(env, v):
    """
    Get the type scheme of a variable.  The variable must have a type scheme.
    """
    return (v.getSystemFTranslation() or env[v]).getTypeScheme()

def assumeType(env, v, information):
    """
    Extend the environment with a type assignment for v.
    """
    assert isinstance(information, TypeAssignment)
    assert v not in env
    env[v] = information

def generalize(gamma, constraints, ty):
    # Determine which type variables to generalize over
    ftv_ty = ty.freeTypeSymbols()
    ftv_gamma = gamma.freeVariables()
    qvars = ftv_ty.difference(ftv_gamma)

    # Determine which constraints to generalize over
    (retained, deferred) = hmtype.splitConstraints(constraints,
                                                   ftv_gamma,
                                                   qvars)

    return (deferred, hmtype.TyScheme(list(qvars.iterStreamTags()),
                                      list(qvars.iterTyVars()),
                                      retained, ty))

def generalizeGroup(gamma, constraints, explicit_qvars, ty_list):
    # Determine which type variables to generalize over
    ftv_ty = hmtype.FreeVariableSet()
    for ty in ty_list: ty.addFreeTypeSymbols(ftv_ty)
    ftv_gamma = gamma.freeVariables()
    local_vars = ftv_ty.difference(ftv_gamma)

    # Determine which constraints to generalize over
    (retained, deferred) = hmtype.splitConstraints(constraints,
                                                   ftv_gamma,
                                                   local_vars)

    # Create type schemes
    schemes = []
    for x_qvars, ty in zip(explicit_qvars, ty_list):
        # Determine which variables the type scheme is parameterized over.
        qvars_set = ty.freeTypeSymbols().difference(ftv_gamma)

        # If no explicit type variables are given, then we should not
        # parameterize over any rigid type variables.
        if x_qvars is None:
            for v in qvars_set.iterTyVars():
                if isinstance(v, hmtype.RigidTyVar):
                    raise TypeCheckError, "Type is less polymorphic than expeced"

        # Otherwise, we should parameterize over only the given type variables.
        # It's acceptable to parameterize over a subset.
        # All variables in the set are rigid.
        else:
            for v in qvars_set.iterTyVars():
                if v not in x_qvars:
                    raise TypeCheckError, "Type is more polymorphic than expected"

        # The retained constraints must only mention these variables
        for c in retained:
            if not c.freeVariables().issubset(set(qvars_set.iterTyVars())):
                raise TypeCheckError, "Ambiguous type variable in constraint"

        # Do not parameterize over any stream tag variables
        sch = hmtype.TyScheme([], list(qvars_set.iterTyVars()), retained, ty)
        schemes.append(sch)

    return (deferred, retained, schemes)

def assignGeneralizedType(gamma, v, ty, constraints):
    """
    assignGeneralizedType(Environment, TyVar, FirstOrderType, constraints)
        -> constraints

    Generalize the type and constraints to a type scheme.
    Assign the type @ty to @v.  The assignment is recorded globally.
    A new environment and the deferred constraints are returned.
    """
    assert isinstance(v, ast.ANFVariable)
    assert isinstance(ty, hmtype.FirstOrderType)
    for c in constraints: assert isinstance(c, hmtype.ClassPredicate)
    assert v not in gamma

    deferred, scm = generalize(gamma, constraints, ty)
    gamma[v] = PolymorphicAssignment(scm, sf.mkVarE(v.getSystemFVariable()))
    return deferred

def assignGeneralizedTypes(gamma, assignments, constraints):
    """
    assignGeneralizedTypes(Environment, sequence((TyVar, [RigidTyVar] or None, FirstOrderType)), constraints)
        -> (deferred constraints, retained constraints)

    Generalize a list of types in a common context.  All types in the list will
    have the same quantified variables and constraints.
    """
    vars, explicit_qvars, types = unzip3(assignments)

    # Generalize with a common context
    (deferred, retained, schemes) = generalizeGroup(gamma, constraints,
                                                    explicit_qvars, types)

    # Assign each type
    for v, scm in itertools.izip(vars, schemes):
        gamma[v] = PolymorphicAssignment(scm, sf.mkVarE(v.getSystemFVariable()))
    return (deferred, retained)

###############################################################################
# Helper functions for collecting results

def unzip(xs):
    """
    unzip : [(a, b)] -> ([a], [b])
    """
    ys = []
    zs = []
    for y,z in xs:
        ys.append(y)
        zs.append(z)
    return (ys, zs)

def unzip3(xs):
    """
    unzip3 : [(a, b, c)] -> ([a], [b], [c])
    """
    ws = []
    ys = []
    zs = []
    for w,y,z in xs:
        ws.append(w)
        ys.append(y)
        zs.append(z)
    return (ws, ys, zs)

# Many functions return lists of constraints and placeholders.
# These lists form a monoid under concatenation.
unitCPh = ([], [])

def catCPh(*args):
    if len(args) == 1:
        constraints = []
        placeholders = []
        for c, p in args[0]:
            constraints.extend(c)
            placeholders.extend(p)
        return (constraints, placeholders)
    elif len(args) == 2:
        (c1, p1), (c2, p2) = args
        return (c1 + c2, p1 + p2)
    else:
        raise TypeError, "Expecting one or two arguments"

def isValidCPh((constraints, placeholders)):
    for c in constraints:
        if not isinstance(c, hmtype.ClassPredicate):
            return False

    for ph in placeholders:
        if not isinstance(ph, (RecVarPlaceholder, DictPlaceholder)):
            return False

    return True

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
    Create a dictionary environment.  Assign a fresh System-F variable to each
    constraint.  The variable represents the class dictionary for the
    constraint.
    """
    return [(c, sf.newVar(None)) for c in constraints]

def makePolymorphicFunction(gamma, dict_env, name, old_parameters, old_body, body_type):
    """
    makePolymorphicFunction(Environment, dict(Constraint, ObVariable),
                            anf.ANFVariable, [sf.Pat], sf.Exp, sf.type)
        -> sf.Def

    Given the System F translation of a first-order function,
    add extra parameters that turn it into the System F translation of a
    polymorphic function.  The extra parameters are type parameters and
    dictionary parameters, derived from the 'qvars' and 'constraints' fields
    of the type.
    """
    scm = findVariableTypeScheme(gamma, name)

    # Use the dictionary environment to determine dictionary parameters.
    # Dictionary environment's constraints are the same as the type
    # scheme's constraints.
    dict_parameters = [sf.mkVarP(v, d.getDictionaryType())
                       for d, v in dict_env]

    # Convert the type parameters to type variables.
    type_parameters = [sf.mkTyPat(gluon_types.convertVariable(t),
                                  gluon_types.convertKind(t.getKind()))
                       for t in scm.qvars]

    new_fn = sf.mkFun(type_parameters,
                      dict_parameters + old_parameters,
                      gluon_types.convertType(body_type),
                      gluon_types.convertStreamTag(body_type),
                      old_body)
    return sf.mkDef(name.getSystemFVariable(), new_fn)

def findConstraintDictionary(dict_env, constraint):
    """
    findConstraintDictionary([(ClassPredicate, ANFVariable)], ClassPredicate)
        -> (placeholders, sf.Expression) or None

    Generate a dictionary for the given constraint from the dictionary
    environment.  If it can't be generated, return None.
    """
    # Get the derivation of this constraint
    derivation, hnf_predicates = constraint.toHNF()
    placeholders, expr = derivation.getCode(dict_env)

    # If an IdDerivation was returned and it became a placeholder, then
    # no progress was made
    if isinstance(derivation, IdDerivation) and placeholders: return None

    # Otherwise, use the results
    return (placeholders, expr)

def updateDictPlaceholder(gamma, dict_env, placeholder):
    """
    Update a placeholder that represents a class dictionary.
    """
    assert isinstance(placeholder, DictPlaceholder)

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
    assert isinstance(placeholder, RecVarPlaceholder)

    result_type = placeholder.getFirstOrderType()
    variable = placeholder.getVariable()
    
    # The variable should have a type scheme now.
    scm = findVariableTypeScheme(gamma, variable)

    # Instantiate the type scheme, then unify it with the inferred type to
    # get the real type of this instance.  Unification must succeed, because
    # type inference has succeeded.
    tyvars, constraints, inst_result_type = scm.instantiate()
    try: unification.unify(inst_result_type, result_type)
    except UnificationError, e:
        raise RuntimeError, "Dictionary elaboration failed"

    # Create the call expression
    var_expr = sf.mkVarE(variable.getSystemFVariable())
    new_placeholders, expr = \
        gluon_types.makeInstanceExpression(tyvars, constraints, var_expr)

    # Try to resolve dictionary parameters now
    unresolved_placeholders = []
    for ph in new_placeholders:
        unresolved_placeholders += updateDictPlaceholder(gamma, dict_env, ph)
    del new_placeholders

    # Record the resolution for this placeholder
    placeholder.setElaboration(expr)

    # Return the unresolved dictionary placeholders
    return unresolved_placeholders

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
        if isinstance(ph, RecVarPlaceholder):
            new_phs = updateRecVarPlaceholder(gamma, dict_env, ph)
        elif isinstance(ph, DictPlaceholder):
            new_phs = updateDictPlaceholder(gamma, dict_env, ph)
        else:
            raise TypeError, type(ph)

        deferred.extend(new_phs)

    return deferred

###############################################################################
# Type inference

def inferLetBindingType(gamma, param, bound_constraints, bound_type, expr):
    """
    inferLetBindingType(Environment, ast.Parameter, constraints,
                        FirstOrderType, ast.Expression)
        -> (constraints, sf.Pat)

    Infer types in a let-binding.  Bound variables are assigned a
    first-order type.
    The expression 'expr' is only used for error reporting.  The types are
    added to the environment.

    Returns a list of deferred constraints, and a type-annotated parameter.
    """

    if param is None:
        # Use a wildcard parameter.
        return (bound_constraints,
                sf.mkWildP(gluon_types.convertType(bound_type)))

    elif isinstance(param, ast.TupleParam):
        # Unify the bound type with a tuple type
        field_types = [hmtype.TyVar(kind.Star()) for _ in param.fields]

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

        return (csts, sf.mkTupleP(new_params))

    elif isinstance(param, ast.VariableParam):
        if False:
            # Generalize this type
            csts = assignGeneralizedType(gamma, param.name, bound_type,
                                         bound_constraints)
        else:
            # Assign a monomorphic type
            v = sf.mkVarE(param.name.getSystemFVariable())
            assumeType(gamma, param.name, FirstOrderAssignment(bound_type, v))
            csts = bound_constraints

        scm = gamma[param.name].getTypeScheme()
        return (csts, sf.mkVarP(param.name.getSystemFVariable(),
                                gluon_types.convertType(scm)))

    else:
        raise TypeError, type(param)

def exposeParameterBinding(gamma, param):
    """
    exposeParameterBinding(gamma, ast.Parameter)
        -> (sf.Parameter, FirstOrderType)
    Create new types for a first-order parameter binding.
    The environment is updated with type assumptions for bound variables.
    The parameter and its type are returned.
    """

    if isinstance(param, ast.TupleParam):
        new_fields, types = exposeParameterBindings(gamma, param.fields)
        return (sf.mkTupleP(new_fields), hmtype.tupleType(types))

    elif isinstance(param, ast.VariableParam):
        # If this parameter's type has been declared, use that type;
        # otherwise, create a new type variable
        t = param.annotation or hmtype.TyVar(kind.Star())
        v = param.name

        sf_expr = sf.mkVarE(v.getSystemFVariable())
        assumeType(gamma, v, FirstOrderAssignment(t, sf_expr))
        return (sf.mkVarP(v.getSystemFVariable(),
                          gluon_types.convertType(t)), t)

    else:
        raise TypeError, type(param)

def exposeParameterBindings(gamma, params):
    """
    Expose a list of first-order parameter bindings.
    The environment is updated with all bindings.
    A new set of parameters and their types are returned.
    """
    # Expose bindings, updating the environment
    return unzip(exposeParameterBinding(gamma, p) for p in params)

def exposeRecursiveVariable(gamma, v):
    """
    exposeRecursiveVariable(gamma, v) -> first-order type

    Create new first-order types for a variable defined in a recursive
    binding group.
    The environment is updated with types and dictionary-passing placeholder
    information.
    """
    # Create a new type variable for this parameter
    t = hmtype.TyVar(kind.Star())
    assumeType(gamma, v, RecursiveAssignment(v, t))
    return t

def exposeRecursiveVariables(gamma, vars):
    return [exposeRecursiveVariable(gamma, v) for v in vars]

def inferFunctionTypeAndReturnParts(gamma, func):
    """
    inferFunctionType(Environment, ast.Function)
        -> ((constraints, placeholders),
            ([sf.Pat], sf.Exp, FirstOrderType, FirstOrderType))

    Infer the type of a function.  Return the function's parameters and body.
    """
    # Create local environment by extending gamma with the function parameters
    local_env = Environment(gamma)
    parameters, param_types = \
        exposeParameterBindings(local_env, func.parameters)

    # Process body
    (csts, placeholders), (body, body_type) = \
        inferExpressionType(local_env, func.body)

    # Check return type against the annotated type, if there is any
    if func.annotation:
        try: fn_ret_type = unification.unify(body_type, func.annotation)
        except unification.UnificationError, e:
            raise TypeCheckError, "Return type does not unify with the annotated type"

    fn_type = hmtype.functionType(param_types, body_type)

    return ((csts, placeholders), (parameters, body, body_type, fn_type))

def inferFunctionType(gamma, func):
    """
    inferFunctionType(Environment, ast.Function)
        -> ((constraints, placeholders), (sf.Fun, FirstOrderType))

    Infer the type of a function.  Return a system-F function.
    """
    (cph, (parameters, body, body_type, fn_type)) = \
        inferFunctionTypeAndReturnParts(gamma, func)

    # Create a function.  It has no type parameters.
    new_func = sf.mkFun([], parameters, gluon_types.convertType(body_type),
                        gluon_types.convertStreamTag(body_type),
                        body)

    return (cph, (new_func, fn_type))

def inferDefGroup(gamma, group):
    """
    inferDefGroup(gamma, [ast.FunctionDef])
        -> ((constraints, placeholders), [sf.FunctionDef])

    Infer types in a definition group.  Each function in the group is assigned
    a type scheme.  The definition group's type assignments are returned as a
    new environment.
    """

    # Describe the variables bound by the definition group
    bound_vars = [d.name for d in group]

    # For each definition, get the annotated parameter variables
    explicit_qvars = [d.function.qvars for d in group]
    
    # Make a local copy of the environment containing the mutually recursive
    # definitions.  The definitions are given first-order types in the local
    # environment.
    rec_gamma = Environment(gamma)

    # Add definitions to a local copy of the environment
    binding_types = exposeRecursiveVariables(rec_gamma, bound_vars)

    # Infer all function types in the definition group.
    # Return the rewritten functions.
    def inferFun(d, d_type):
        (fn_csts, fn_ph), (fn_params, fn_body, fn_body_type, fn_type) = \
            inferFunctionTypeAndReturnParts(rec_gamma, d.function)

        # Unify the function's assumed type with the inferred type
        try: unification.unify(fn_type, d_type)
        except unification.UnificationError, e:
            raise TypeCheckError, "Type error in recursive definition group"

        return ((fn_csts, fn_ph), (d.name, fn_params, fn_body, fn_body_type))

    # The functions in the definition group will have the same
    # class constraint context.
    # This performs unification, setting binding_types to the correct
    # first-order types for this definition group.
    (group_csts, group_phs), new_group_functions = \
        collectCPh(inferFun(*x) for x in zip(group, binding_types))

    # Generalize the function types
    # Note that we generalize with the environment that will be seen in
    # subsequent code (gamma), not the local environment
    deferred_csts, retained_csts = \
        assignGeneralizedTypes(gamma,
                               zip(bound_vars, explicit_qvars, binding_types),
                               group_csts)

    # Build function definitions; add System F parameters
    dict_env = makeDictionaryEnvironment(retained_csts)

    new_group = [makePolymorphicFunction(gamma, dict_env, name, fn_params,
                                         fn_body, fn_body_type)
                 for name, fn_params, fn_body, fn_body_type
                 in new_group_functions]

    # Update recursive variable placeholders
    deferred_phs = updateRecVarPlaceholders(gamma, dict_env, group_phs)

    return ((deferred_csts, deferred_phs), new_group)

def inferExpressionType(gamma, expr):
    """
    inferExpressionType(Environment, ast.Expression)
        -> ((constraints, placeholders), (sf.Expression, FirstOrderType))

    Infer the type of an expression in environment @env.
    Return a new copy of the expression; the returned expression's type is
    stored in its 'type' field.
    """
    assert isinstance(gamma, Environment)
    assert isinstance(expr, ast.Expression)

    # Structural recursion.  Infer types of subexpressions.
    # In each branch:
    #   put the new, typed expression in 'new_expr'
    #   put its type in 'new_expr_type'
    #   put the list of constraints and placeholders in 'cph'
    #   do not update the environment
    if isinstance(expr, ast.VariableExpr):
        # If the variable has a type scheme, then instantiate it.
        # Otherwise, look up its type in the environment.
        cph, (new_expr, new_expr_type) = \
            instantiateVariable(gamma, expr.variable)

    elif isinstance(expr, ast.LiteralExpr):
        new_expr_type = literalSignature(expr.literal)
        sf_type = gluon_types.convertType(new_expr_type)
        if isinstance(expr.literal, bool):
            literal = sf.mkBoolL(expr.literal)
        elif isinstance(expr.literal, int):
            literal = sf.mkIntL(expr.literal)
        elif isinstance(expr.literal, float):
            literal = sf.mkFloatL(expr.literal)
        elif expr.literal is None:
            literal = sf.NoneL
        else:
            raise TypeError, type(expr.literal)
        new_expr = sf.mkLitE(literal, sf_type)
        cph = unitCPh

    elif isinstance(expr, ast.IfExpr):
        cph_cond, (cond, cond_type) = \
            inferExpressionType(gamma, expr.argument)
        try:
            unification.unify(cond_type, builtin_data.type_bool)
        except unification.UnificationError, e:
            print_ast.printAst(expr.argument)
            raise TypeCheckError, "Condition of 'if' expression msut be a boolean"
        cph_true, (if_true, if_true_type) = \
            inferExpressionType(gamma, expr.ifTrue)
        cph_false, (if_false, if_false_type) = \
            inferExpressionType(gamma, expr.ifFalse)

        try:
            new_expr_type = unification.unify(if_true_type, if_false_type)
        except unification.UnificationError, e:
            print_ast.printAst(expr)
            raise TypeCheckError, "Branches of 'if' expression have different types"

        new_expr = sf.mkIfE(cond, if_true, if_false)
        cph = catCPh((cph_cond, cph_true, cph_false))

    elif isinstance(expr, ast.TupleExpr):
        # Process subexpressions
        cph, args_types = collectCPh(inferExpressionType(gamma, arg)
                                     for arg in expr.arguments)
        args, arg_types = unzip(args_types)

        # Construct tuple type
        new_expr_type = hmtype.tupleType(arg_types)
        new_expr = sf.mkTupleE(args)

    elif isinstance(expr, ast.CallExpr):
        # Infer types of subexpressions
        cph_oper, (oper, oper_type) = inferExpressionType(gamma, expr.operator)
        cph_args, args_types = \
            collectCPh(inferExpressionType(gamma, arg)
                               for arg in expr.arguments)
        args, arg_types = unzip(args_types)

        # Create function type; unify
        new_expr_type = hmtype.TyVar(kind.Star())
        try: unification.unify(oper_type,
                               hmtype.functionType(arg_types, new_expr_type))
        except unification.UnificationError, e:
            print_ast.printAst(expr)
            print "Function type:", pretty.renderString(oper_type.pretty())
            print "Argument types:", ", ".join([pretty.renderString(at.pretty()) for at in arg_types])
            raise TypeCheckError, "Type mismatch in function call (" + str(e) + ")"

        new_expr = sf.mkCallE(oper, args)
        cph = catCPh(cph_oper, cph_args)

    elif isinstance(expr, ast.LetExpr):
        # Process the RHS
        (csts_rhs, ph_rhs), (rhs, rhs_type) = \
            inferExpressionType(gamma, expr.rhs)

        # Bind the LHS
        # The deferred constraints and local environment will be used while
        # processing the body
        local_gamma = Environment(gamma)
        csts_rhs_deferred, lhs = \
            inferLetBindingType(local_gamma, expr.parameter, csts_rhs,
                                rhs_type, expr)

        # Process the body
        cph_body, (body, new_expr_type) = \
            inferExpressionType(local_gamma, expr.body)

        new_expr = sf.mkLetE(lhs, rhs, body)
        cph = catCPh((csts_rhs_deferred, ph_rhs), cph_body)

    elif isinstance(expr, ast.LetrecExpr):
        # Process the local functions and assign type schemes
        local_gamma = Environment(gamma)
        cph_group, def_group = inferDefGroup(local_gamma, expr.definitions)

        # Infer body of letrec
        cph_body, (body, new_expr_type) = inferExpressionType(local_gamma, expr.body)

        new_expr = sf.mkLetrecE(def_group, body)
        cph = catCPh(cph_group, cph_body)

    elif isinstance(expr, ast.UndefinedExpr):
        new_expr_type = hmtype.TyVar(kind.Star())
        new_expr = sf.mkUndefinedE(gluon_types.convertType(new_expr_type))
        cph = unitCPh

    elif isinstance(expr, ast.FunExpr):
        cph, (fun, new_expr_type) = inferFunctionType(gamma, expr.function)
        new_expr = sf.mkFunE(fun)

    else:
        raise TypeError, type(expr)

    # Save and return the computed type
    assert sf.isExp(new_expr)
    assert isinstance(new_expr_type, hmtype.FirstOrderType)
    assert isValidCPh(cph)

    return (cph, (new_expr, new_expr_type))

def doTypeInference(anf_form):
    assert isinstance(anf_form, ast.Module)

    global_gamma = Environment()
    new_groups = []
    for defgroup in anf_form.iterDefinitionGroups():
        (csts, placeholders), new_group = \
            inferDefGroup(global_gamma, defgroup)
        assert not csts     # There should be no deferred constraints here
        assert not placeholders # All placeholders should have been resolved
        new_groups.append(new_group)

    return sf.makeAndEvaluateModule(sum(new_groups, []))

def inferTypes(anf_form):
    return doTypeInference(anf_form)

