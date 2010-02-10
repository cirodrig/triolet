# printast.py
#
# Prints the AST in human-readable form

from pyon.ast.ast import *
import pyon.pretty as pretty
import pyon.ast.operators
import sys 

#_indentation = 0

def printAst(root, file = sys.stdout):
    """A generic, recursive printing function.
    Examines the argument type and calls the appropriate print function.

    root: an AST node marking the subtree to be printed"""
#    _indentation = 0
    if isinstance(root, Expression):
        doc = printExpression(root, _OUTER_PREC)
    elif isinstance(root, FunctionDef):
        doc = printFuncDef(root)
    elif isinstance(root, Function):
        doc = printLambdaFunction(root)
    elif isinstance(root, Variable):
        doc = printVar(root)
    elif isinstance(root, Parameter):
        doc = printParam(root)
    elif isinstance(root, Module):
        doc = printModule(root)
    else:
        raise TypeError("Called printAst on a non-AST object")

    pretty.render(pretty.stack(doc, ''), file)

# Precedences, used for inserting parentheses
_OUTER_PREC = 0
_LAM_PREC = 1
_IF_PREC = 1
_APP_PREC = 2

def printType(expr, t, type_variables = None):
    assert isinstance(t, hmtype.PyonTypeBase)
    if type_variables is None:
        type_variables = t.freeVariables()
    return t.showWorker(hmtype.PyonTypeBase.PREC_OUTER, list(type_variables))

def printExpression(expr, precedence, type_variables = None):
    """
    Returns a pretty-printable object for an expression IR node

    expr: Expression node in the AST
    precedence: Operator precedence implied by context
    """
    if type_variables is None:
        type_variables = set()
        expr.addAllTypeVariables(type_variables)

    def printRec(expr, precedence):
        return printExpression(expr, precedence, type_variables)

    if isinstance(expr, VariableExpr):
        return printVar(expr.variable)

    elif isinstance(expr, LiteralExpr):
        lit = expr.literal
        if lit is None:
            return "None"
        elif isinstance(lit, (int, float, bool)):
            return lit
        else:
            raise TypeError, type(lit)

    elif isinstance(expr, IfExpr):
        ifdoc = pretty.space("if", printRec(expr.argument, _IF_PREC))
        thendoc = pretty.space("then",
                               printRec(expr.ifTrue, _IF_PREC))
        elsedoc = pretty.space("else",
                               printRec(expr.ifFalse, _IF_PREC))
        doc = pretty.stack([ifdoc, thendoc, elsedoc])
        if precedence >= _IF_PREC: doc = pretty.parens(doc)
        return doc

    elif isinstance(expr, TupleExpr):
        # Insert a comma at the end, if it's a 1-element-tuple 
        args = expr.arguments
        if len(args) == 1:
            fs = pretty.abut(printRec(args[0], _OUTER_PREC), ',')
        else:
            argdocs = [printRec(e, _OUTER_PREC) for e in expr.arguments]
            fs = pretty.space(pretty.punctuate(',', argdocs)) 
        return pretty.parens(fs)

    elif isinstance(expr, UndefinedExpr):
        return "__undefined__"

    elif isinstance(expr, CallExpr):
        arglist = pretty.punctuate(',', [printRec(e, _OUTER_PREC)
                                         for e in expr.arguments])
        operator = printRec(expr.operator, _APP_PREC)
        doc = pretty.abut(operator, pretty.parens(pretty.space(arglist)))
        if precedence >= _APP_PREC: doc = pretty.parens(doc)
        return doc

    elif isinstance(expr, LetExpr):
        if expr.parameter is None:
            paramdoc = '_'
        else:
            paramdoc = printParam(expr.parameter, type_variables)
        rhsdoc = printRec(expr.rhs, _OUTER_PREC)
        assndoc = pretty.stack(pretty.space(['let', paramdoc, '=']),
                               pretty.nest(pretty.abut(rhsdoc, ';'), 4))
        bodydoc = printRec(expr.body, _OUTER_PREC)
        return pretty.stack(assndoc, bodydoc)
    elif isinstance(expr, LetrecExpr):
        defdoclist = pretty.punctuate(';',
                                      [printFuncDef(f, type_variables)
                                       for f in expr.definitions])
        return pretty.stack(['letrec', pretty.bracesStack(defdoclist, 2),
                             printRec(expr.body, _OUTER_PREC)])
    elif isinstance(expr, FunExpr):
        doc = printLambdaFunction(expr.function, type_variables)
        if precedence >= _LAM_PREC: doc = pretty.parens(doc)
        return doc
    elif isinstance(expr, DictPlaceholderExpr):
        doc = pretty.abut('PLACEHOLDER',
                          pretty.parens(expr.getConstraint().pretty(type_variables)))
        return doc
    elif isinstance(expr, RecVarPlaceholderExpr):
        doc = pretty.abut('PLACEHOLDER',
                          pretty.parens(printVar(expr.getVariable())))
        return doc
    else:
        raise TypeError, type(expr)

def printLambdaFunction(func, type_variables):
    paramdoc = pretty.punctuate(',', [printParam(p, type_variables) for p in func.parameters])
    bodydoc = printExpression(func.body, _LAM_PREC, type_variables)
    return pretty.stack(pretty.abut(pretty.space(['lambda'] + paramdoc), ':'),
                        pretty.nest(bodydoc, 4))

def printFuncDef(fdef, type_variables = None):
    """Returns a pretty-printable object for a FunctionDef node in the AST

    fdef: FunctionDef to be printed"""
    if type_variables is None:
        type_variables = set()
        fdef.addAllTypeVariables(type_variables)

    func = fdef.function

    # Begin with syntax that resembles a function call
    paramdoc = pretty.punctuate(',', [printParam(p, type_variables)
                                      for p in func.parameters])
    paramdoc = pretty.parens(pretty.space(paramdoc))

    scm = fdef.name.getTypeScheme()
    if scm:
        typedoc = pretty.abut(pretty.space([printVar(fdef.name, shadowing = False),
                                            ':', scm.prettyUnshadowed(type_variables)]),
                              ';')
    else:
        typedoc = None
    calldoc = pretty.abut(printVar(fdef.name), paramdoc)
    bodydoc = printExpression(func.body, _OUTER_PREC, type_variables)
    return pretty.stack([typedoc,
                         pretty.space(calldoc, '='),
                         pretty.nest(bodydoc, 4)])

def printVar(v, shadowing = True):
    """Returns a pretty-printable object for a variable in the AST
    v: Variable to be printed"""
    # If variable is anonymous, print a dollar-sign
    return pretty.abut(v.name or '$', v.identifier)

def printParam(p, type_variables = None):
    """Returns a pretty-printable object for a parameter in the AST
    TupleParams untested as of yet...
    p: Parameter to be printed"""
    if type_variables is None:
        type_variables = set()
        fdef.addAllTypeVariables(type_variables)

    if isinstance(p, VariableParam):
        if p.annotation is not None:
            pass #Unimplemented?

        scm = p.name.getTypeScheme()
        if scm: typedoc = pretty.space(':', scm.pretty(type_variables))
        else: typedoc = None

        return pretty.space(printVar(p.name), typedoc)
    elif isinstance(p, TupleParam):
        fields = [printParam(f, type_variables) for f in p.fields]
        return pretty.braces(pretty.space(pretty.punctuate(',', fields)))
    else:
        raise TypeError('Called printParam with unknown param type')

def printModule(m, type_variables = None):
    """Returns a pretty-printable object for a Module in the AST
    As of yet untested.
    m: Module to be printed"""
    if type_variables is None:
        type_variables = set()
        m.addAllTypeVariables(type_variables)

    def defgroup(dg):
        return [printFuncDef(d, type_variables) for d in dg]

    defdoclist = [pretty.bracesStack(pretty.punctuate(';', defgroup(dg)))
                  for dg in m.definitions]

    return pretty.stack('module', pretty.bracesStack(defdoclist))

