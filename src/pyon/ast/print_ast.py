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

def printExpression(expr, precedence):
    """
    Returns a pretty-printable object for an expression IR node

    expr: Expression node in the AST
    precedence: Operator precedence implied by context
    """
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
        ifdoc = pretty.space("if", printExpression(expr.argument, _IF_PREC))
        thendoc = pretty.space("then",
                               printExpression(expr.ifTrue, _IF_PREC))
        elsedoc = pretty.space("else",
                               printExpression(expr.ifFalse, _IF_PREC))
        doc = pretty.stack([ifdoc, thendoc, elsedoc])
        if precedence >= _IF_PREC: doc = pretty.parens(doc)
        return doc

    elif isinstance(expr, TupleExpr):
        # Insert a comma at the end, if it's a 1-element-tuple 
        args = expr.arguments
        if len(args) == 1:
            fs = pretty.abut(printExpression(args[0], _OUTER_PREC), ',')
        else:
            argdocs = [printExpression(e, _OUTER_PREC)
                       for e in expr.arguments]
            fs = pretty.space(pretty.punctuate(',', argdocs)) 
        return pretty.parens(fs)

    elif isinstance(expr, UndefinedExpr):
        return "__undefined__"

    elif isinstance(expr, CallExpr):
        arglist = pretty.punctuate(',', [printExpression(e, _OUTER_PREC)
                                         for e in expr.arguments])
        operator = printExpression(expr.operator, _APP_PREC)
        doc = pretty.abut(operator, pretty.parens(pretty.space(arglist)))
        if precedence >= _APP_PREC: doc = pretty.parens(doc)
        return doc

    elif isinstance(expr, LetExpr):
        paramdoc = printParam(expr.parameter)
        rhsdoc = printExpression(expr.rhs, _OUTER_PREC)
        assndoc = pretty.stack(pretty.space(['let', paramdoc, '=']),
                               pretty.nest(pretty.abut(rhsdoc, ';'), 4))
        bodydoc = printExpression(expr.body, _OUTER_PREC)
        return pretty.stack(assndoc, bodydoc)
    elif isinstance(expr, LetrecExpr):
        defdoclist = pretty.punctuate(';',
                                      [printFuncDef(f)
                                       for f in expr.definitions])
        return pretty.stack(['letrec', pretty.bracesStack(defdoclist, 2),
                             printExpression(expr.body, _OUTER_PREC)])
    elif isinstance(expr, FunExpr):
        doc = printLambdaFunction(expr.function)
        if precedence >= _LAM_PREC: doc = pretty.parens(doc)
        return doc
    else:
        raise TypeError, type(expr)

def printLambdaFunction(func):
    paramdoc = pretty.punctuate(',', [printParam(p) for p in func.parameters])
    bodydoc = printExpression(func.body, _LAM_PREC)
    return pretty.stack(pretty.abut(pretty.space(['lambda'] + paramdoc), ':'),
                        pretty.nest(bodydoc, 4))

def printFuncDef(fdef):
    """Returns a pretty-printable object for a FunctionDef node in the AST

    fdef: FunctionDef to be printed"""
    # Begin with syntax that resembles a function call
    paramdoc = pretty.punctuate(',', [printParam(p)
                                      for p in fdef.function.parameters])
    scm = fdef.name.getTypeScheme()
    if scm:
        typedoc = pretty.abut(pretty.space([printVar(fdef.name),
                                            ':', scm.pretty()]),
                              ';')
    else:
        typedoc = None
    calldoc = pretty.abut(printVar(fdef.name),
                          pretty.parens(pretty.space(paramdoc)))
    return pretty.stack([typedoc,
                         pretty.space(calldoc, '='),
                         pretty.nest(printExpression(fdef.function.body, _OUTER_PREC), 4)])

def printVar(v):
    """Returns a pretty-printable object for a variable in the AST
    v: Variable to be printed"""
    # If variable is anonymous, print a dollar-sign
    return pretty.abut(v.name or '$', v.identifier)

def printParam(p):
    """Returns a pretty-printable object for a parameter in the AST
    TupleParams untested as of yet...
    p: Parameter to be printed"""
    if isinstance(p, VariableParam):
        if p.annotation is not None:
            pass #Unimplemented?

        scm = p.name.getTypeScheme()
        if scm: typedoc = pretty.space(':', scm.pretty())
        else: typedoc = None

        return pretty.space(printVar(p.name), typedoc)
    elif isinstance(p, TupleParam):
        return pretty.braces(pretty.space(pretty.punctuate(',', [printParam(f) for f in p.fields])))
    else:
        raise TypeError('Called printParam with unknown param type')

def printModule(m):
    """Returns a pretty-printable object for a Module in the AST
    As of yet untested.
    m: Module to be printed"""
    def defgroup(dg):
        return [printFuncDef(d) for d in dg]

    defdoclist = [pretty.bracesStack(pretty.punctuate(';', defgroup(dg)))
                  for dg in m.definitions]

    return pretty.stack('module', pretty.bracesStack(defdoclist))

