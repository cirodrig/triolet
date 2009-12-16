# Conversion from Python ASTs to ANF
# This file is very incomplete.

# TODO: How to convert control flow?

import pyon.ast.parser_ast as p_ast
import pyon.ast.anf_ast as a_ast

def convertModule(module):
    "Convert a module to ANF"
    return a_ast.Module([[convertFunction(f) for f in dg]
                         for dg in module.definitions])

def convertFunction(func):
    "Convert a parser function to an ANF function definition"

    # Convert to the SSA name
    name = convertVariable(func.name, func.ssaver)

    # Convert parameters
    parameters = [convertParameter(p) for p in func.parameters]

    # Convert body
    body = convertSuite(func.body, _consumeValue(func.joinPoint))

    return a_ast.FunctionDef(name, a_ast.Function(parameters, body))
             
def convertSuite(suite, make_fallthrough):
    """
    Convert a suite of statements together with a fallthrough path.
    The fallthrough path is executed if the statements terminates with a
    fall-through (not a return).
    """
    def convertSuiteMember(i):
        # To convert the i_th element of the suite, call convertStatement.
        # The fallthrough path for the i_th element is the i+1_th element,
        # so pass a function that converts the i+1_th element of the suite
        # as a parameter.  When we reach the end of the list, pass the
        # make_fallthrough function.
        if i < len(suite):
            return lambda: convertStatement(suite[i], convertSuiteMember(i+1))
        else:
            return make_fallthrough
    return convertSuiteMember(0)

def convertStatement(stmt, make_fallthrough):
    """
    Convert a statement to an ANF statement.  The code for the fallthrough
    path is passed as the second parameter.
    """
    if isinstance(stmt, ExprStmt):
        # let _ = first in next
        first = convertExpression(stmt.expression)
        return a_ast.LetExpr(None, first, make_fallthrough())

    elif isinstance(stmt, AssignStmt):
        # let x = first in next
        first = convertExpression(stmt.expression)
        lhs = convertParameter(stmt.lhs)
        return a_ast.LetExpr(lhs, first, make_fallthrough())

    elif isinstance(stmt, ReturnStmt):
        return _produceValue(stmt)

    elif isinstance(stmt, IfStmt):
        join_node = stmt.joinPoint

        cond = convertExpression(stmt.cond)

        # If there's a return statement inside the block, then generate code
        # on each path
        # FIXME: Doing it this way may cause code duplication.  We really
        # should use a letrec if there will be code duplication.
        if join_node.hasret:
            true_path = convertSuite(stmt.ifTrue, make_fallthrough)
            false_path = convertSuite(stmt.ifFalse, make_fallthrough)
            return a_anf.IfExpr(cond, true_path, false_path)
        else:
            # let (x, y) = (if cond then true_path else false_path) in next
            true_path = convertSuite(stmt.ifTrue, returnValue)
            false_path = convertSuite(stmt.ifFalse, returnValue)
            param = _consumeValue(stmt.joinNode)
            if_expr = a_anf.IfExpr(cond, true_path, false_path)
            return a_anf.LetExpr(param, if_expr, make_fallthrough())

    elif isinstance(stmt, DefGroupStmt):
        defs = [convertFunctionDef(d) for d in stmt.definitions]
        return a_ast.LetrecExpr(defs, make_fallthrough())

    else:
        raise TypeError, type(stmt)

def returnValue(tuple_expr): return tuple_expr

def _produceValue(stmt):
    """
    Create a tuple expression with the values of the live-in variables of
    join_node on the path coming from stmt.
    """
    def find_var(variable, phi_node):
        """
        Create an expression corresponding to the value of 'variable'.
        """
        # Search for the path from the current statement into the phi node
        for (phi_stmt, version) in phi_node.paths:
            if stmt is phi_stmt: break
        else:
            raise KeyError, "Missing SSA information for a control flow path"

        # Convert to an ANF variable
        return convertVariable(variable, version)

    values = [a_ast.VariableExpr(find_var(var, phi_node))
              for var, phi_node in stmt.joinPoint.phiNodes]

    return a_ast.TupleExpr(values)

def _consumeValue(join_point):
    """
    Create a parameter expression with the live-in variables of join_node.
    """
    values = [a_ast.VariableParam(var, phi_node.ssaver)
              for var, phi_node in join_point.phiNodes]
    return a_ast.TupleParam(values)

def convertExpression(expr):
    "Convert a parser expression to an ANF expression"
    if isinstance(expr, p_ast.VariableExpr):
        return a_ast.VariableExpr(expr.variable, expr.ssaver)

    elif isinstance(expr, p_ast.LiteralExpr):
        return a_ast.LiteralExpr(expr.literal)

    elif isinstance(expr, p_ast.TupleExpr):
        return a_ast.TupleExpr([convertExpression(e) for e in expr.arguments])

    elif isinstance(expr, p_ast.UnaryExpr):
        return a_ast.CallExpr(convertUnaryOperator(expr.operator),
                              [convertExpression(expr.argument)])

    elif isinstance(expr, p_ast.BinaryExpr):
        return a_ast.CallExpr(convertBinaryOperator(expr.operator),
                              [convertExpression(expr.left),
                               convertExpression(expr.right)])

    elif isinstance(expr, p_ast.ListCompExpr):
        # Convert the comprehension [blah for blah in blah] to a
        # function call list(blah for blah in blah)
        return a_ast.CallExpr(builtins.func_list,
                              [a_ast.IterExpr(convertIterator(expr.iterator))])

    elif isinstance(expr, p_ast.GeneratorExpr):
        return a_ast.IterExpr(convertIterator(expr.iterator))

    elif isinstance(expr, p_ast.CallExpr):
        return a_ast.CallExpr(convertExpression(expr.operator),
                              [convertExpression(e) for e in expr.arguments])

    elif isinstance(expr, p_ast.CondExpr):
        return a_ast.IfExpr(convertExpression(expr.argument),
                            convertExpression(expr.ifTrue),
                            convertExpression(expr.ifFalse))

    elif isinstance(expr, p_ast.LambdaExpr):
        parameters = [convertParameter(p) for p in expr.parameters]
        body = convertExpression(expr.body)
        return a_ast.FunExpr(a_ast.Function(a_ast.Function.EXPRESSION,
                                            parameters, body))

    else:
        raise TypeError, type(p_ast)

def convertVariable(var, ssaver):
    """
    convertVariable(PythonVariable, ssa-version) -> ANFVariable
    Convert a variable to ANF.  The SSA version is used to pick
    an identifier for the variable.
    """
    # Choose an identifier for this variable
    try:
        n = var.ssaVersionMap[ssaver]
    except KeyError:
        n = var.ssaVersionMap[ssaver] = ANFVariable.getNewID()

    return ANFVariable(var.name, n)
