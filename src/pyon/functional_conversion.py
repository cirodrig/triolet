"Convert the parser AST data structures to an untyped functional form."

import gluon
import untyped
import pyon.ast.operators as operators
import pyon.ast.parser_ast as p_ast
import pyon.ssa.parser_ssa as ssa

###############################################################################
# Type and kind conversion

def convertAnnotatedKind(annotation):
    "Convert a kind annotation to an actual kind"
    assert isinstance(annotation, p_ast.Expression)

    # Kinds can be the arrow kind (k1 -> k2) or the base kind (*)
    if isinstance(annotation, p_ast.BinaryExpr):
        param_k = convertAnnotatedKind(annotation.left)
        result_k = convertAnnotatedKind(annotation.right)
        return untyped.ArrowK(param_k, result_k)

    elif isinstance(annotation, p_ast.VariableExpr):
        if not annotation.variable.anfKind:
            raise RuntimeError, "Not a kind"
        return annotation.variable.anfKind

    else:
        raise RuntimeError, "Not a valid kind expression"

def getAnnotatedFuncType(annotation, a_tyvars):
    "Convert function type annotation to an actual function type"
    assert isinstance(annotation, p_ast.BinaryExpr)
    assert annotation.operator == operators.ARROW

    param_ty = getAnnotatedFuncParams(annotation.left, a_tyvars)
    ret_ty = convertAnnotation(annotation.right, a_tyvars)

    t = untyped.functionType(param_ty, ret_ty)
    return t

def getAnnotatedFuncParams(annotation, a_tyvars):
    "Get list of function parameter(s)"
    params = []

    def addParameters(expr):
        # If a parameter list is given, process the left side of the list
        # recursively, then the right side.
        if isinstance(expr, p_ast.BinaryExpr):
            if expr.operator == operators.MUL:
                addParameters(expr.left)
                params.append(convertAnnotation(expr.right, a_tyvars))
            else:
                raise TypeError, expr.operator.name
        else:
            params.append(convertAnnotation(expr, a_tyvars))

    addParameters(annotation)

    return params

def getAnnotatedAppType(operator, arguments, a_tyvars):
    "Convert a type application to a type"
    oper_ty = convertAnnotation(operator, a_tyvars)
    arg_tys =[convertAnnotation(a, a_tyvars) for a in arguments]
    return untyped.typeApplication(oper_ty, arg_tys)

def convertAnnotation(annotation, a_tyvars):
    "Convert type annotation to corresponding type"
    if isinstance(annotation, p_ast.VariableExpr):
        # If there's a pre-assigned type, return it
        if annotation.variable.anfType:
            return annotation.variable.anfType

        # If there's any other pre-assigned other meaning, then raise an error
        if annotation.variable.hasANFDefinition():
            raise RuntimeError, "Not a type"
        
        # Otherwise, this variable should represent a type variable
        try: return a_tyvars[annotation.variable]
        except: raise RuntimeError, "Not a type"

    elif isinstance(annotation, p_ast.TupleExpr):
        t = untyped.tupleType([convertAnnotation(arg, a_tyvars)
                               for arg in annotation.arguments])
        return t

    elif isinstance(annotation, p_ast.BinaryExpr):
        if annotation.operator == operators.ARROW:
            t = getAnnotatedFuncType(annotation, a_tyvars)
            return t
        else:
            raise TypeError, annotation.operator.name

    elif isinstance(annotation, p_ast.CallExpr):
        t = getAnnotatedAppType(annotation.operator, annotation.arguments,
                                a_tyvars)
        return t

    else:
        raise TypeError, type(annotation)

def convertAnnotatedType(p, kind_annotation):
    "Convert type variable annotation to non-unifiable type variable"
    if kind_annotation:
        k = convertAnnotatedKind(kind_annotation)
    else:
        # Default to kind '*'
        k = untyped.Star

    return untyped.RigidTyVar(gluon.pgmLabel("pyonfile", p.name), k)

###############################################################################
# Top-level routine

def convertModule(module):
    functions = [[convertFunction({}, f) for f in dg]
                 for dg in module.definitions]
    exports = [convertExport(e) for e in module.exports]
    return untyped.Module(functions, exports)

def convertExport(export):
    # Convert to the SSA name
    name = convertVariable(export.name, export.ssaver)

    return untyped.Export(export.sourcePos, name)

###############################################################################
# Function conversion

def convertFunction(outer_tyvars, func):
    # Convert to the SSA name
    name = convertVariable(func.name, func.ssaver)

    # Get annotated type variables and merge with already defined
    if func.qvars is not None:
        new_qvars = [convertAnnotatedType(p, k) for p, k in func.qvars]
        a_tyvars = dict(zip([p for p, _ in func.qvars], new_qvars))
        a_tyvars.update(outer_tyvars)
    else:
        new_qvars = None
        a_tyvars = outer_tyvars

    # Convert annotated return type
    if func.annotation:
        annotation = convertAnnotation(func.annotation, a_tyvars)
    else:
        annotation = None

    # Convert parameters
    parameters = [convertParameter(a_tyvars, p) for p in func.parameters]

    # Convert body
    def cannot_fallthrough(*args):
        # Control flow should never "fall through" out of a function body;
        # It should always end at a return statement
        raise ValueError, "Function body has no fallthrough path"
    body = convertSuite(func.body, cannot_fallthrough, a_tyvars)

    return untyped.Def(name,
                       untyped.Function(func.sourcePos, new_qvars, parameters,
                                        annotation, body))

def convertSuite(suite, make_fallthrough, a_tyvars):
    """
    Convert a suite of statements together with a fallthrough path.
    The fallthrough path is executed if the statements terminates with a
    fall-through (not a return).
    """
    suite_len = len(suite)

    # Start at the end and work backwards
    suite_expr = convertControlStatement(suite[-1], make_fallthrough)
    for stmt in reversed(suite[:-1]):
        suite_expr = convertStatement(stmt, suite_expr, a_tyvars)

    return suite_expr

def convertControlStatement(stmt, make_fallthrough):
    """
    Convert a control flow statement to an untyped statement.  The continuation
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

def convertStatement(stmt, successor, a_tyvars):
    """
    Convert a statement to an untyped expression.  The following statement
    is passed as the second parameter.  The following statement will appear
    exactly once in the generated untyped code.
    """
    if isinstance(stmt, p_ast.ExprStmt):
        # let _ = first in next
        first = convertExpression(a_tyvars, stmt.expression)
        return untyped.LetE(stmt.sourcePos, untyped.WildP(), first, successor)

    elif isinstance(stmt, p_ast.AssignStmt):
        # let x = first in next
        first = convertExpression(a_tyvars, stmt.expression)
        lhs = convertParameter(a_tyvars, stmt.lhs)
        return untyped.LetE(stmt.sourcePos, lhs, first, successor)

    elif isinstance(stmt, p_ast.IfStmt):
        join_node = stmt.joinPoint

        cond = convertExpression(a_tyvars, stmt.cond)

        # If there is no escaping control, generate an if-else expression
        if not join_node.hasret:
            # let (x, y) = (if cond then true_path else false_path) in next

            # Create the if-else expression
            def returnValue(live_outs):
                # Return a tuple of the live-out variables
                return untyped.TupleE(stmt.sourcePos, live_outs)

            true_path = convertSuite(stmt.ifTrue, returnValue, a_tyvars)
            false_path = convertSuite(stmt.ifFalse, returnValue, a_tyvars)
            if_expr = untyped.IfE(stmt.sourcePos, cond, true_path, false_path)

            # Create the subsequent code
            param = untyped.TupleP(_consumeValue(join_node))
            return untyped.LetE(stmt.sourcePos, param, if_expr, successor)

        # If there's exactly one fallthrough path, then generate code
        # on each path and inline the continuation
        elif join_node.hasft == 1:
            # if cond then true_path else false_path

            # The fallthrough path will be incorporated into any
            # branches of the if expression that fall through
            def make_join(live_outs):
                # Make a 'let' expression for each variable
                ret_val = successor
                for pattern, value in reversed(zip(_consumeValue(join_node),
                                                   live_outs)):
                    ret_val = untyped.LetE(stmt.sourcePos,
                                           pattern, value, ret_val)
                return ret_val

            true_path = convertSuite(stmt.ifTrue, make_join, a_tyvars)
            false_path = convertSuite(stmt.ifFalse, make_join, a_tyvars)
            return untyped.IfE(stmt.sourcePos, cond, true_path, false_path)

        # Otherwise, generate a local function for the continuation
        else:
            # let k (x1, x2 ... xn) = successor
            # in if cond then true_path else false_path

            # The name of the continuation function
            cont_var = untyped.Variable(None)

            # The live-ins of the continuation.  Unpack the tuple.
            params = _consumeValue(join_node)

            # Define the continuation function
            cont_fun = untyped.Function(stmt.sourcePos,
                                        None, params, None, successor)

            # At the end of the if/else branches, call the continuation
            # function
            def make_join(live_outs):
                return untyped.CallE(stmt.sourcePos,
                                     untyped.VariableE(stmt.sourcePos,
                                                       cont_var),
                                     live_outs)

            # Define the if-else expression
            true_path = convertSuite(stmt.ifTrue, make_join, a_tyvars)
            false_path = convertSuite(stmt.ifFalse, make_join, a_tyvars)
            if_expr = untyped.IfE(stmt.sourcePos, cond, true_path, false_path)

            return untyped.LetrecE(stmt.sourcePos,
                                   [untyped.Def(cont_var, cont_fun)],
                                   if_expr)

    elif isinstance(stmt, p_ast.DefGroupStmt):
        defs = [convertFunction(a_tyvars, d) for d in stmt.definitions]
        return untyped.LetrecE(stmt.sourcePos, defs, successor)

    else:
        raise TypeError, type(stmt)

def _produceValue(control_flow_stmt):
    """
    Create the values of the live-in variables of
    join_node on the path coming from stmt.
    """
    join_node = control_flow_stmt.joinNode

    def find_var(variable, phi_node):
        """
        Create an expression corresponding to the value of 'variable'.
        """
        version = phi_node.getVersion(variable, control_flow_stmt)
        return convertVariableRef(control_flow_stmt.sourcePos,
                                  variable, version)

    values = [find_var(var, phi_node)
              for var, phi_node in join_node.phiNodes.iteritems()]

    return values

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
    return convertVariableRef(control_flow_stmt.sourcePos, var, version)

def _consumeValue(join_point):
    """
    Create a list of parameter expressions.  Each parameter is one live-in
    variable of join_node.
    """
    return [untyped.VariableP(convertVariable(var, phi_node.ssaVersion))
            for var, phi_node in join_point.phiNodes.iteritems()]

def convertExpression(a_tyvars, expr):
    "Convert a parser expression to an untyped expression"
    if isinstance(expr, p_ast.VariableExpr):
        return convertVariableRef(expr.sourcePos, expr.variable, expr.ssaver)

    elif isinstance(expr, p_ast.TupleExpr):
        return untyped.TupleE(expr.sourcePos,
                              [convertExpression(a_tyvars, e)
                               for e in expr.arguments])

    elif isinstance(expr, p_ast.LiteralExpr):
        l = expr.literal
        if l is None:
            return untyped.NoneLiteral(expr.sourcePos)
        elif isinstance(l, bool):
            return untyped.BoolLiteral(expr.sourcePos, l)
        elif isinstance(l, float):
            return untyped.FloatLiteral(expr.sourcePos, l)
        elif isinstance(l, int):
            return untyped.IntLiteral(expr.sourcePos, l)
        else:
            raise TypeError, type(l)

    elif isinstance(expr, p_ast.UnaryExpr):
        return _callVariable(expr.sourcePos,
                             convertUnaryOperator(expr.operator),
                             [convertExpression(a_tyvars, expr.argument)])

    elif isinstance(expr, p_ast.BinaryExpr):
        return _callVariable(expr.sourcePos,
                             convertBinaryOperator(expr.operator),
                             [convertExpression(a_tyvars, expr.left),
                              convertExpression(a_tyvars, expr.right)])

    elif isinstance(expr, p_ast.ListCompExpr):
        # Convert the comprehension [blah for blah in blah] to a
        # function call list(blah for blah in blah)
        iter = convertIterator(a_tyvars, expr.iterator)
        return _callVariable(expr.sourcePos, untyped.fun_makelist, [iter])

    elif isinstance(expr, p_ast.GeneratorExpr):
        return convertIterator(a_tyvars, expr.iterator)

    elif isinstance(expr, p_ast.CallExpr):
        return untyped.CallE(expr.sourcePos,
                             convertExpression(a_tyvars, expr.operator),
                             [convertExpression(a_tyvars, e)
                              for e in expr.arguments])

    elif isinstance(expr, p_ast.CondExpr):
        return untyped.IfE(expr.sourcePos,
                           convertExpression(a_tyvars, expr.argument),
                           convertExpression(a_tyvars, expr.ifTrue),
                           convertExpression(a_tyvars, expr.ifFalse))

    elif isinstance(expr, p_ast.LambdaExpr):
        parameters = [convertParameter(a_tyvars, p) for p in expr.parameters]
        body = convertExpression(a_tyvars, expr.body)
        return untyped.FunE(expr.sourcePos,
                            untyped.Function(expr.sourcePos,
                                             None, parameters, None, body))

    else:
        raise TypeError, type(p_ast)

def convertIterator(a_tyvars, iter):
    "Convert an iterator to an untyped iterator expression"
    if isinstance(iter, p_ast.ForIter):
        arg = convertExpression(a_tyvars, iter.argument)
        
        # Convert the body to a function
        param = convertParameter(a_tyvars, iter.parameter)
        body_func = untyped.Function(iter.sourcePos, None, [param], None,
                                     convertIterator(a_tyvars, iter.body))

        # Call __iter__ on the thing being traversed
        iterator = _callVariable(iter.sourcePos, untyped.fun_iter, [arg])

        # Create a call to iterBind
        return _callVariable(iter.sourcePos, untyped.fun_iterBind,
                             [iterator, untyped.FunE(iter.sourcePos,
                                                     body_func)])
    elif isinstance(iter, p_ast.IfIter):
        # Convert guard and body
        guard = convertExpression(a_tyvars, iter.guard)
        body = convertIterator(a_tyvars, iter.body)

        # Create a call to 'GUARD'
        return _callVariable(iter.sourcePos, untyped.fun_guard, [guard, body])
    elif isinstance(iter, p_ast.DoIter):
        # create a call to 'DO'
        body = convertExpression(a_tyvars, iter.body)
        return _callVariable(iter.sourcePos, untyped.fun_do, [body])
    else:
        raise TypeError, type(iter)

def convertParameter(a_tyvars, param):
    "Convert a parser parameter to an untyped parameter"
    if isinstance(param, p_ast.VariableParam):
        var = convertVariable(param.name, param.ssaver)

        # Convert annotated parameter type
        if param.annotation:
            annotation = convertAnnotation(param.annotation, a_tyvars)
        else:
            annotation = None

        return untyped.VariableP(var, annotation)
    elif isinstance(param, p_ast.TupleParam):
        return untyped.TupleP([convertParameter(a_tyvars, p)
                               for p in param.fields])
    else:
        raise TypeError, type(param)

def convertVariable(var, ssaver):
    """
    convertVariable(PythonVariable, ssa-version) -> Variable
    Convert a variable to an untyped variable.  The SSA version is used to pick
    an identifier for the variable.
    """
    assert ssaver != -1
    assert ssaver != ssa.notSSA

    # Choose an identifier for this variable
    try:
        v = var.ssaVersionMap[ssaver]
    except KeyError:
        if var.name: label = gluon.pgmLabel("pyonfile", var.name)
        else: label = None
        v = untyped.Variable(label)
        var.ssaVersionMap[ssaver] = v

    return v

def convertVariableRef(sourcePos,var, ssaver):
    """
    convertVariableRef(PythonVariable, ssa-version) -> Expression
    Convert a variable reference to an ANF expression.  The SSA
    version is used to pick an identifier for the variable.  If the
    SSA version is -1, then an undefined expression is returned.
    """
    # If version is -1, then use the special expression 'undefined'
    if ssaver == -1:
        return untyped.UndefinedE(sourcePos)

    # If not tracked by SSA, then return the pre-assigned value.
    # It must be a variable, not a type.
    elif ssaver == ssa.notSSA:
        t = var.anfVariable
        if not t:
            raise RuntimeError, "Not a variable"
        return untyped.VariableE(sourcePos, t)
    else:
        return untyped.VariableE(sourcePos, convertVariable(var, ssaver))

# A mapping from parser operator to ANF variable
_convertBinaryOperatorMap = {
    operators.ADD       : untyped.oper_ADD,
    operators.SUB       : untyped.oper_SUB,
    operators.MUL       : untyped.oper_MUL,
    operators.DIV       : untyped.oper_DIV,
    operators.MOD       : untyped.oper_MOD,
    operators.FLOORDIV  : untyped.oper_FLOORDIV,
    operators.POWER     : untyped.oper_POWER,
    operators.EQ        : untyped.oper_EQ,
    operators.NE        : untyped.oper_NE,
    operators.LT        : untyped.oper_LT,
    operators.LE        : untyped.oper_LE,
    operators.GT        : untyped.oper_GT,
    operators.GE        : untyped.oper_GE,
    operators.BITWISEAND : untyped.oper_BITWISEAND,
    operators.BITWISEOR : untyped.oper_BITWISEOR,
    operators.BITWISEXOR : untyped.oper_BITWISEXOR
    }

def convertBinaryOperator(oper):
    """
    Return the untyped variable denoting a binary operator.
    """
    # The arrow should only be used in type expressions
    if oper == operators.ARROW:
        raise RuntimeError, "'->' used as a binary operator"

    try: return _convertBinaryOperatorMap[oper]
    except KeyError:
        raise KeyError, "Cannot find variable for binary operator " + \
            oper.display

# A mapping from parser operator to ANF variable
_convertUnaryOperatorMap = {
    operators.NEGATE    : untyped.oper_NEGATE
    }

def convertUnaryOperator(oper):
    """
    Return the untyped variable denoting a unary operator.
    """
    try: return _convertUnaryOperatorMap[oper]
    except KeyError:
        raise KeyError, "Cannot find variable for unary operator " + \
            oper.display

def _callVariable(sourcePos, func, arguments):
    """
    Create the ANF code for a function call to a variable.
    """
    return untyped.CallE(sourcePos,
                         untyped.VariableE(sourcePos, func),
                         arguments)
