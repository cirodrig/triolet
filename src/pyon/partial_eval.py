"""
Partial evaluation transformations used to optimize and simplify Pyon code.
These transformations operate on typed, dictionary-passing Pyon code.

The transformations are constant and copy propagation, inlining, and
specialization.

The output of this module may have internal data structure sharing.  Avoid
mutating it.  Variable names may be reused in the output, but names obey the
no-shadowing rule: a name is never bound in a place where that name is already
in scope.
"""

import itertools
import pyon.ast.ast as ast
import pyon.ast.print_ast as print_ast

def _isValueExpr(expr):
    """
    Return True only if the expression has no side effects.  This is used to
    determine whether to inline/copy-propagate.

    We currently return False for some obviously side-effect-free expressions,
    but this could be improved.
    """
    if isinstance(expr, (ast.VariableExpr, ast.LiteralExpr, ast.UndefinedExpr,
                         ast.FunExpr,
                         ast.DictionaryBuildExpr, ast.DictionarySelectExpr)):
        return True
    elif isinstance(expr, (ast.CallExpr, ast.IfExpr, ast.LetExpr,
                           ast.LetrecExpr)):
        return False
    elif isinstance(expr, ast.TupleExpr):
        for e in expr.arguments:
            if not _isValueExpr(e): return False
        return True
    else:
        raise TypeError, type(expr)

def _parameterVariables(param):
    """Get a list of all variables bound by this parameter"""
    if param is None: return []
    if isinstance(param, ast.VariableParam):
        return [param.name]
    elif isinstance(param, ast.TupleParam):
        return sum((_parameterVariables(p) for p in param.fields), [])
    else:
        raise TypeError, type(param)

###############################################################################
# A dictionary of variable assignments is used for inlining.
# Each variable that is a candidate for inlining has instructions about whether
# and how to inline it.

class Inline(object):
    def __init__(self, *args):
        raise NotImplementedError

    def getValue(self):
        raise NotImplementedError

class InlineNever(Inline):
    _singleton = None
    def __new__(cls):
        if not InlineNever._singleton:
            InlineNever._singleton = Inline.__new__(cls)
        return InlineNever._singleton

    def __init__(self): pass

    def getValue(self):
        raise RuntimeError, "Cannot inline"
    
class InlineAlways(object):
    "A directive to always inline"
    def __init__(self, value):
        assert isinstance(value, ast.Expression)
        self._value = value

    def getValue(self): return self._value

class InlineDict(object):
    "A directive to inline if it enables specialization"
    def __init__(self, value):
        assert isinstance(value, ast.Expression)
        self._value = value

    def getValue(self): return self._value

###############################################################################
# Eliminate redundant let-bindings.
# Traverse expressions bottom-up, collecting the set of names mentioned at each
# level.

def _elimDeadCodeMap(f, exprs):
    variables = set()
    new_exprs = []
    for e in exprs:
        (s, e2) = f(e)
        variables.update(s)
        new_exprs.append(e2)
    return (variables, new_exprs)

def _elimDeadCodeExprs(exprs):
    """
    _elimDeadCodeExprs(expressions) -> (variable set, new expressions)
    Remove dead assignments from a list of expressions.  Return the
    set of variables mentioned in the expressions.
    """
    return _elimDeadCodeMap(_elimDeadCodeExpr, exprs)

def _elimDeadCodeFunDefs(exprs):
    """
    _elimDeadCodeFunDefs(definitions) -> (variable set, new definitions)
    Remove dead assignments from a list of function definitions.  Return the
    set of variables mentioned in the definitions.
    """
    return _elimDeadCodeMap(_elimDeadCodeFunDef, exprs)

def _elimDeadCodeExpr(expr):
    """
    _elimDeadCodeExpr(expression) -> (variable set, new expression)
    Remove dead assignments from an expression.  Return the simplified
    expression and the set of variables mentioned in it.
    """

    # Boring structural recursion for most expression types.
    # The interesting cases are LetExpr and LetrecExpr.
    if isinstance(expr, ast.VariableExpr):
        return (set([expr.variable]), expr)
    elif isinstance(expr, (ast.LiteralExpr, ast.UndefinedExpr)):
        return (set(), expr)
    elif isinstance(expr, ast.TupleExpr):
        (s, arguments) = _elimDeadCodeExprs(expr.arguments)
        return (s, ast.TupleExpr(arguments, base = ast.copyTypedExpr(expr)))
    elif isinstance(expr, ast.DictionaryBuildExpr):
        (s, scs) = _elimDeadCodeExprs(expr.superclasses)
        (s2, ms) = _elimDeadCodeExprs(expr.methods)
        s.update(s2)
        return (s, ast.DictionaryBuildExpr(expr.cls, scs, ms,
                                           base = ast.copyTypedExpr(expr)))
    elif isinstance(expr, ast.DictionarySelectExpr):
        (s, argument) = _elimDeadCodeExpr(expr.argument)
        return (s, ast.DictionarySelectExpr(expr.cls, expr.index, argument,
                                            base = ast.copyTypedExpr(expr)))
    elif isinstance(expr, ast.CallExpr):
        (s, operator) = _elimDeadCodeExpr(expr.operator)
        (s2, arguments) = _elimDeadCodeExprs(expr.arguments)
        s2.update(s)
        return (s2, ast.CallExpr(operator, arguments,
                                 base = ast.copyTypedExpr(expr)))
    elif isinstance(expr, ast.IfExpr):
        (s, cond) = _elimDeadCodeExpr(expr.argument)
        (s2, if_true) = _elimDeadCodeExpr(expr.ifTrue)
        (s3, if_false) = _elimDeadCodeExpr(expr.ifFalse)
        s.update(s2)
        s.update(s3)
        return (s, ast.IfExpr(cond, if_true, if_false,
                              base = ast.copyTypedExpr(expr)))
    elif isinstance(expr, ast.FunExpr):
        (s, f) = _elimDeadCodeFunc(expr.function)
        return (s, ast.FunExpr(f, base = ast.copyTypedExpr(expr)))

    elif isinstance(expr, ast.LetExpr):
        # If the LHS _is_ the body, then simplify to the RHS.
        #   let x = foobar in x  --->  foobar
        if isinstance(expr.body, ast.VariableExpr) and \
           isinstance(expr.parameter, ast.VariableParam) and \
           expr.body.variable == expr.parameter.name:
            # Replace this expression with its RHS, and proces the RHS
            return _elimDeadCodeExpr(expr.rhs)

        # Structural recursion
        (rhs_s, rhs) = _elimDeadCodeExpr(expr.rhs)
        (body_s, body) = _elimDeadCodeExpr(expr.body)
        param_vars = _parameterVariables(expr.parameter)

        # Find which bound variables are mentioned in the body.
        # Remove all bound variables from the set of used variables.
        mentioned_in_body = False
        for v in param_vars:
            if v in body_s:
                mentioned_in_body = True
                body_s.discard(v)
                
        # If no bound variables are mentioned in the body, then eliminate the
        # variable binding.  If, furthermore, the RHS is a value, then
        # eliminate the RHS, leaving only the body.
        if mentioned_in_body:
            body_s.update(rhs_s)
            return (body_s, ast.LetExpr(expr.parameter, rhs, body,
                                        base = ast.copyTypedExpr(expr)))
        elif _isValueExpr(rhs):
            return (body_s, body)
        else:
            body_s.update(rhs_s)
            return (body_s, ast.LetExpr(None, rhs, body,
                                        base = ast.copyTypedExpr(expr)))

    elif isinstance(expr, ast.LetrecExpr):
        (s, body) = _elimDeadCodeExpr(expr.body)
        (new_s, defs) = _elimDeadCodeDefGroup(expr.definitions, s)

        # If no local functions were kept, return only the body
        if not defs: return (s, body)

        return (new_s, ast.LetrecExpr(defs, body,
                                      base = ast.copyTypedExpr(expr)))

    else:
        raise TypeError, type(expr)

def _elimDeadCodeFunc(func):
    # Process function body
    (s, body) = _elimDeadCodeExpr(func.body)

    # Remove function parameters from the mentions set
    for param in itertools.chain(func.parameters,
                                 func.dictionaryParameters or []):
        for param_var in _parameterVariables(param):
            s.discard(param_var)

    return (s, ast.Function(func.parameters, body,
                            dictionary_parameters = func.dictionaryParameters,
                            type = func.type))

def _elimDeadCodeFunDef(fun_def):
    (s, function) = _elimDeadCodeFunc(fun_def.function)
    return (s, ast.FunctionDef(fun_def.name, function))

def _elimDeadCodeDefGroup(def_group, mentioned_set = None):
    """
    _elimDeadCodeDefGroup(definition group, [variable set])
        -> (variable set, new definition group)

    Eliminate dead code in a definition group.
    If mentioned_set is None, then preserve all definitions.  Otherwise,
    discard definitions that are not referenced (transitively) by
    @mentioned_set.

    Returns the set of variables mentioned in the definition group or in
    the input set (if given).
    """
    # Process function definitions
    defs = [_elimDeadCodeFunDef(d) for d in def_group]
    num_defs = len(defs)

    # Mark the definitions that are mentioned, including
    # transitive mentions.
    if mentioned_set is not None:
        defs_mentioned = [False] * num_defs
        defs_worklist = [mentioned_set]
        while defs_worklist:
            current_set = defs_worklist.pop()

            # Scan each definition
            for index in range(num_defs):
                (fundef_s, fundef) = defs[index]
                # If unmarked and reachable
                if not defs_mentioned[index] and fundef.name in current_set:
                    # Mark and add to worklist
                    defs_mentioned[index] = True
                    defs_worklist.append(fundef_s)
    else:
        # Assume that all functions were mentined
        defs_mentioned = [True] * num_defs

    # Collect the marked definitions and mentions sets
    new_defs = []
    if mentioned_set is None: new_s = set()
    else: new_s = set(mentioned_set)
    for (fundef_s, fundef), is_mentioned in zip(defs, defs_mentioned):
        if is_mentioned:
            new_defs.append(fundef)
            new_s.update(fundef_s)

    # Remove locally bound names
    for d in new_defs: new_s.discard(d.name)

    # Return the new definitions and set
    return (new_s, new_defs)

def eliminateDeadCode(module):
    # Keep all global-scope definitions
    new_definitions = []
    for dg in reversed(module.definitions):
        (_, new_dg) = _elimDeadCodeDefGroup(dg, None)
        new_definitions.append(new_dg)
        
    return ast.Module(new_definitions)

###############################################################################
# Partial evaluation.  Try to evaluate expressions.

# Default partial evaluation context 
_CTX_DEFAULT = 0

# Dictionary partial evaluation context: used in a dictionary select expression
_CTX_DICT = 1

def _evalDictionarySelectExpr(cls, index, argument):
    # Simplify a dictionary-select expression to just the selected value
    assert isinstance(argument, ast.DictionaryBuildExpr)

    return argument.methods[index]

def _bindLetPattern(env, pattern, expr):
    """
    Bind the pattern to the expression in the environment.  The environment
    is updated.
    """
    if pattern is None: return
    
    if isinstance(pattern, ast.VariableParam):
        # If it's a simple value, always inline it.
        # Otherwise, skip it.
        if _isValueExpr(expr):
            env[pattern.name] = InlineAlways(expr)

    elif isinstance(pattern, ast.VariableParam):
        # If it's a tuple expression, unpack it.
        # Otherwise, skip it.
        if isinstance(expr, TupleExpr):
            # Tuple sizes must match
            assert len(expr.arguments) == len(pattern.fields)

            # Bind each tuple parameter
            for field, arg in zip(pattern.fields, expr.arguments):
                _bindLetPattern(env, field, arg)

def _pevalExpr(env, expr, context = _CTX_DEFAULT):
    """
    Perform partial evaluation on an expression.  Return an equivalent
    expression.  The return value may be a previously created object.
    The environment is not modified.
    """
    if isinstance(expr, ast.VariableExpr):
        # Look up this variable in the environment to decide what to replace
        # it with
        assignment = env.get(expr.variable)

        # No mapping: leave it alone
        if not assignment: return expr

        # Always inline: insert the expression here
        if isinstance(assignment, InlineAlways):
            return assignment.getValue()

        # Dictionary inline: insert if in dictionary context
        if isinstance(assignment, InlineDict) and context == _CTX_DICT:
            return assignment.getValue()

        # Otherwise, no change
        return expr

    elif isinstance(expr, (ast.LiteralExpr, ast.UndefinedExpr)):
        return expr

    elif isinstance(expr, ast.TupleExpr):
        return ast.TupleExpr([_pevalExpr(env, f) for f in expr.arguments],
                             base = ast.copyTypedExpr(expr))

    elif isinstance(expr, ast.DictionaryBuildExpr):
        sc = [_pevalExpr(env, f) for f in expr.superclasses]
        methods = [_pevalExpr(env, f) for f in expr.methods]
        return ast.DictionaryBuildExpr(expr.cls, sc, methods,
                                   base = ast.copyTypedExpr(expr))

    elif isinstance(expr, ast.DictionarySelectExpr):
        argument = _pevalExpr(env, expr.argument, _CTX_DICT)

        # Can we simplify this expression?
        if isinstance(argument, ast.DictionaryBuildExpr):
            new_expr = _evalDictionarySelectExpr(expr.cls, expr.index,
                                                 argument)
        else:
            new_expr = ast.DictionarySelectExpr(expr.cls, expr.index,
                                                argument,
                                                base = ast.copyTypedExpr(expr))
        return _evaluate(env, new_expr)

    elif isinstance(expr, ast.CallExpr):
        oper = _pevalExpr(env, expr.operator)
        args = [_pevalExpr(env, f) for f in expr.arguments]
        return ast.CallExpr(oper, args, base = ast.copyTypedExpr(expr))

    elif isinstance(expr, ast.IfExpr):
        oper = _pevalExpr(env, expr.argument)
        if_true = _pevalExpr(env, expr.ifTrue)
        if_false = _pevalExpr(env, expr.ifFalse)
        return ast.IfExpr(oper, if_true, if_false,
                          base = ast.copyTypedExpr(expr))

    elif isinstance(expr, ast.FunExpr):
        func = _pevalFunc(env, expr.function)
        return ast.FunExpr(func, base = ast.copyTypedExpr(expr))

    elif isinstance(expr, ast.LetExpr):
        # Evaluate the RHS
        rhs = _pevalExpr(env, expr.rhs)

        # Add it to the environment (make a copy)
        env = dict(env)
        _bindLetPattern(env, expr.parameter, rhs)

        # Process the body
        body = _pevalExpr(env, expr.body)

        return ast.LetExpr(expr.parameter, rhs, body,
                           base = ast.copyTypedExpr(expr))

    elif isinstance(expr, ast.LetrecExpr):
        defs = _pevalDefGroup(env, expr.definitions)

        # FIXME: Add letrec-bound functions to the environment
        # This enables inlining
        body = _pevalExpr(env, expr.body)
        return ast.LetrecExpr(defs, body, base = ast.copyTypedExpr(expr))

    else:
        raise TypeError, type(expr)
        
def _pevalFunc(env, f):
    "Partial evaluation of one lambda function or named function"
    body = _pevalExpr(env, f.body)
    return ast.Function(f.parameters, body,
                        dictionary_parameters = f.dictionaryParameters,
                        type = f.type)

def _pevalFunDef(env, f):
    func = _pevalFunc(env, f.function)
    return ast.FunctionDef(f.name, func)

def _pevalDefGroup(env, dg):
    "Partial evaluation of one definition group"
    return [_pevalFunDef(env, d) for d in dg]

def partialEval(mod):
    env = dict()

    # Iterate through the definition groups; update environment
    dgs = [_pevalDefGroup(env, dg) for dg in mod.iterDefinitionGroups()]

    return ast.Module(dgs)
