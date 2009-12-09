# Conversion from Python ASTs to ANF
# This file is very incomplete.

# TODO: How to convert control flow?

import pyon.ast.parser_ast as p_ast
import pyon.ast.anf_ast as a_ast

def convertModule(module, scope):
    "Convert a module to ANF"
    return a_ast.Module([[convertGlobalFunction(scope, f)
                          for f in dg]
                         for dg in module.definitions])

def convertGlobalFunction(func scope):
    "Convert a global function to an ANF functon definition"
    anf_func = convertFunction(func, scope)
    new_func = a_ast.FunctionDef(func.name, anf_func)
    return new_func

def convertFunction(func, scope):
    "Convert a function or lambda expression to an ANF function"

    # Get values from the parameter 
    if isinstance(func, p_ast.Function):
        parameters = func.parameters
        body = func.body
        local_scope = func.local_scope
    elif isinstance(func, p_ast.LambdaExpr):
        parameters = func.parameters
        body = func.body
        local_scope = func.local_scope
    else:
        raise TypeError, type(func)

    # Create the function body
    new_parameters = [convertParameter(p, scope) for p in parameters]
    new_body = convertSuite(body,
                            _returnNothing,
                            extendScope(scope, local_scope))
    return a_ast.Function(new_parameters, new_body)

def convertSuite(suite, control_flow, scope):
    "Convert a suite of statements to an ANF expression"
    if len(suite) == 0:
        return _pass

    suite_length = len(suite)

    def convertTail(index):
        # Convert the part of the suite of statements starting at 'index'
        if index == suite_length:
            return convertFinalStatement(suite[index], scope)
        else:
            return convertMedialStatement(suite[index],
                                          convertTail(index + 1),
                                          scope)

    return convertTail(0)

def convertFinalStatement(stmt, scope):
    if isinstance(stmt, ExprStmt):
        return convertExpression(stmt.expr, scope)
    elif isinstance(stmt, AssignStmt):
        # If it's a local variable the assignment unle
