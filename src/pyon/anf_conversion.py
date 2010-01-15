# Conversion from Python ASTs to ANF
# This file is very incomplete.

# TODO: How to convert control flow?

import pyon.ast.operators as operators
import pyon.ast.parser_ast as p_ast
import pyon.ast.ast as a_ast
import pyon.ssa.parser_ssa as ssa

import pyon.builtin_data as builtin_data

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
    def cannot_fallthrough(*args):
        # Control flow should never "fall through" out of a function body;
        # It should always end at a return statement
        raise ValueError, "Function body has no fallthrough path"
    body = convertSuite(func.body, cannot_fallthrough)

    return a_ast.FunctionDef(name, a_ast.exprFunction(parameters, body))
             
def convertSuite(suite, make_fallthrough):
    """
    Convert a suite of statements together with a fallthrough path.
    The fallthrough path is executed if the statements terminates with a
    fall-through (not a return).
    """
    suite_len = len(suite)
    def convertSuiteMember(i):
        # To convert the i_th element of the suite, call convertStatement.
        # The fallthrough path for the i_th element is the i+1_th element,
        # so pass a function that converts the i+1_th element of the suite
        # as a parameter.  When we reach the end of the list, pass the
        # make_fallthrough function.
        if i < suite_len - 1:
            return lambda: convertStatement(suite[i], convertSuiteMember(i+1))
        else:
            return lambda: convertControlStatement(suite[i], make_fallthrough)

    return convertSuiteMember(0)()

def convertControlStatement(stmt, make_fallthrough):
    """
    Convert a control flow statement to an ANF statement.  The continuation
    is passed as the second parameter.  The continuation is a function that
    takes a set of live-out variables as a parameter and returns an
    expression.
    """
    if isinstance(stmt, ssa.FallStmt):
        return make_fallthrough(_produceValue(stmt))
    elif isinstance(stmt, p_ast.ReturnStmt):
        return _produceReturnValue(stmt)
    else:
        raise TypeError, type(stmt)

def convertStatement(stmt, successor):
    """
    Convert a statement to an ANF statement.  The following statement
    is passed as the second parameter, in the form of a nullary function.

    A nullary function is passed because the code may be generated twice.
    This should be fixed in the future by using a local function to avoid
    ever generating code twice.  Then the value can be passed directly.
    """
    if isinstance(stmt, p_ast.ExprStmt):
        # let _ = first in next
        first = convertExpression(stmt.expression)
        return a_ast.LetExpr(None, first, successor())

    elif isinstance(stmt, p_ast.AssignStmt):
        # let x = first in next
        first = convertExpression(stmt.expression)
        lhs = convertParameter(stmt.lhs)
        return a_ast.LetExpr(lhs, first, successor())

    elif isinstance(stmt, p_ast.IfStmt):
        join_node = stmt.joinPoint

        cond = convertExpression(stmt.cond)

        # If there's a return statement inside the block, then generate code
        # on each path
        # FIXME: Doing it this way may cause code duplication.  We really
        # should use a letrec if there will be code duplication.
        if join_node.hasret:
            # The fallthrough path will be incorporated into any
            # branches of the if expression that fall through
            def make_join(live_out_expr):
                param = _consumeValue(join_node)
                return a_ast.LetExpr(param, live_out_expr, successor())

            true_path = convertSuite(stmt.ifTrue, make_join)
            false_path = convertSuite(stmt.ifFalse, make_join)
            return a_ast.IfExpr(cond, true_path, false_path)
        else:
            # let (x, y) = (if cond then true_path else false_path) in next

            # Create the if-else expression
            def returnValue(tuple_expr): return tuple_expr
            true_path = convertSuite(stmt.ifTrue, returnValue)
            false_path = convertSuite(stmt.ifFalse, returnValue)
            if_expr = a_ast.IfExpr(cond, true_path, false_path)

            # Create the subsequent code
            param = _consumeValue(join_node)
            return a_ast.LetExpr(param, if_expr, successor())

    elif isinstance(stmt, p_ast.DefGroupStmt):
        defs = [convertFunction(d) for d in stmt.definitions]
        return a_ast.LetrecExpr(defs, successor())

    else:
        raise TypeError, type(stmt)

def _produceValue(control_flow_stmt):
    """
    Create a tuple expression with the values of the live-in variables of
    join_node on the path coming from stmt.
    """
    join_node = control_flow_stmt.joinNode

    def find_var(variable, phi_node):
        """
        Create an expression corresponding to the value of 'variable'.
        """
        version = phi_node.getVersion(variable, control_flow_stmt)
        return convertVariableRef(variable, version)

    values = [find_var(var, phi_node)
              for var, phi_node in join_node.phiNodes.iteritems()]

    return a_ast.TupleExpr(values)

def _produceReturnValue(control_flow_stmt):
    """
    Create an expression with the value of the live-in variable of
    join_node on the path coming from stmt.  There must be exactly one
    live-in variable.
    """
    join_node = control_flow_stmt.joinNode

    if len(join_node.phiNodes) != 1:
        # There should be exactly one returned value
        raise ValueError, "Expecting one (explicit or implicit) return value"

    # Get the return variable and its corresponding phi node
    [(var, phi_node)] = join_node.phiNodes.iteritems()

    # Get the SSA version
    version = phi_node.getVersion(var, control_flow_stmt)

    # Create an expression
    return convertVariableRef(var, version)

def _consumeValue(join_point):
    """
    Create a parameter expression with the live-in variables of join_node.
    """
    values = [a_ast.VariableParam(convertVariable(var, phi_node.ssaVersion))
              for var, phi_node in join_point.phiNodes.iteritems()]
    return a_ast.TupleParam(values)

def convertExpression(expr):
    "Convert a parser expression to an ANF expression"
    if isinstance(expr, p_ast.VariableExpr):
        return convertVariableRef(expr.variable, expr.ssaver)

    elif isinstance(expr, p_ast.TupleExpr):
        return a_ast.TupleExpr([convertExpression(e) for e in expr.arguments])

    elif isinstance(expr, p_ast.LiteralExpr):
        return a_ast.LiteralExpr(expr.literal)

    elif isinstance(expr, p_ast.UnaryExpr):
        return _callVariable(convertUnaryOperator(expr.operator),
                             [convertExpression(expr.argument)])

    elif isinstance(expr, p_ast.BinaryExpr):
        return _callVariable(convertBinaryOperator(expr.operator),
                             [convertExpression(expr.left),
                              convertExpression(expr.right)])

    elif isinstance(expr, p_ast.ListCompExpr):
        # Convert the comprehension [blah for blah in blah] to a
        # function call list(blah for blah in blah)
        return _callVariable(builtin_data.oper_LIST,
                             [convertIterator(expr.iterator)])

    elif isinstance(expr, p_ast.GeneratorExpr):
        return convertIterator(expr.iterator)

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
        return a_ast.FunExpr(a_ast.exprFunction(parameters, body))

    else:
        raise TypeError, type(p_ast)

def convertIterator(iter):
    "Convert an iterator to an ANF iterator"
    if isinstance(iter, p_ast.ForIter):
        arg = convertExpression(iter.argument)
        
        # Convert the body to a function
        param = convertParameter(iter.parameter)
        body_func = a_ast.iterFunction([param], convertIterator(iter.body))

        # Create a call to 'FOREACH'
        return _callVariable(builtin_data.oper_FOREACH,
                             [arg, a_ast.FunExpr(body_func)])
    elif isinstance(iter, p_ast.IfIter):
        # Convert guard and body to nullary functions
        guard = convertExpression(iter.guard)
        guard_func = a_ast.exprFunction([], guard)
        body = convertIterator(iter.body)
        body_func = a_ast.iterFunction([], body)

        # Create a call to 'GUARD'
        return _callVariable(builtin_data.oper_GUARD,
                             [a_ast.FunExpr(guard_func),
                              a_ast.FunExpr(body_func)])
    elif isinstance(iter, p_ast.DoIter):
        # create a call to 'DO'
        body = convertExpression(iter.body)
        body_func = a_ast.exprFunction([], body)
        return _callVariable(builtin_data.oper_DO,
                             [a_ast.FunExpr(body_func)])
    else:
        raise TypeError, type(iter)

def convertParameter(param):
    "Convert a parser parameter to an ANF parameter"
    if isinstance(param, p_ast.VariableParam):
        var = convertVariable(param.name, param.ssaver)
        return a_ast.VariableParam(var)
    elif isinstance(param, p_ast.TupleParam):
        return a_ast.TupleParam([convertParameter(p) for p in param.fields])
    else:
        raise TypeError, type(param)

def convertVariable(var, ssaver):
    """
    convertVariable(PythonVariable, ssa-version) -> ANFVariable
    Convert a variable to ANF.  The SSA version is used to pick
    an identifier for the variable.
    """
    assert ssaver != -1

    # Choose an identifier for this variable
    try:
        v = var.ssaVersionMap[ssaver]
    except KeyError:
        v = a_ast.ANFVariable(var.name, a_ast.ANFVariable.getNewID())
        var.ssaVersionMap[ssaver] = v

    return v

def convertVariableRef(var, ssaver):
    """
    convertVariableRef(PythonVariable, ssa-version) -> Expression
    Convert a variable reference to an ANF expression.  The SSA
    version is used to pick an identifier for the variable.  If the
    SSA version is -1, then an undefined expression is returned.
    """
    # If version is -1, then use the special expression 'undefined'
    if ssaver == -1:
        return a_ast.UndefinedExpr()
    else:
        return a_ast.VariableExpr(convertVariable(var, ssaver))

# A mapping from parser operator to ANF variable
_convertBinaryOperatorMap = {
    operators.ADD       : builtin_data.oper_ADD,
    operators.SUB       : builtin_data.oper_SUB,
    operators.MUL       : builtin_data.oper_MUL,
    operators.DIV       : builtin_data.oper_DIV,
    operators.MOD       : builtin_data.oper_MOD,
    operators.FLOORDIV  : builtin_data.oper_FLOORDIV,
    operators.POWER     : builtin_data.oper_POWER,
    operators.EQ        : builtin_data.oper_EQ,
    operators.NE        : builtin_data.oper_NE,
    operators.LT        : builtin_data.oper_LT,
    operators.LE        : builtin_data.oper_LE,
    operators.GT        : builtin_data.oper_GT,
    operators.GE        : builtin_data.oper_GE,
    operators.BITWISEAND : builtin_data.oper_BITWISEAND,
    operators.BITWISEOR : builtin_data.oper_BITWISEOR,
    operators.BITWISEXOR : builtin_data.oper_BITWISEXOR
    }

def convertBinaryOperator(oper):
    """
    Return the Pyon ANF variable denoting a binary operator.
    """
    try: return _convertBinaryOperatorMap[oper]
    except KeyError:
        raise KeyError, "Cannot find variable for binary operator " + \
            oper.display

# A mapping from parser operator to ANF variable
_convertUnaryOperatorMap = {
    operators.NEGATE    : builtin_data.oper_NEGATE
    }

def convertUnaryOperator(oper):
    """
    Return the Pyon ANF variable denoting a unary operator.
    """
    try: return _convertUnaryOperatorMap[oper]
    except KeyError:
        raise KeyError, "Cannot find variable for unary operator " + \
            oper.display

def _callVariable(func, arguments):
    """
    Create the ANF code for a function call to a variable.
    """
    return a_ast.CallExpr(a_ast.VariableExpr(func), arguments)