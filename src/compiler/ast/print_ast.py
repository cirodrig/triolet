# printast.py
#
# Prints the AST in human-readable form

from ast import *
from pretty import *
import operators
import sys 

#_indentation = 0

def printAst(root, file = sys.stdout):
    """A generic, recursive printing function.
    Examines the argument type and calls the appropriate print function.

    root: an AST node marking the subtree to be printed"""
#    _indentation = 0
    if isinstance(root, Expression):
        doc = printExpression(root)
    elif isinstance(root, Iterator):
        doc = printIterator(root)
    elif isinstance(root, FunctionDef):
        doc = printFuncDef(root)
    elif isinstance(root, Function):
        doc = printFunction(root)
    elif isinstance(root, Variable):
        doc = printVar(root)
    elif isinstance(root, Parameter):
        doc = printParam(root)
    elif isinstance(root, Module):
        doc = printModule(root)
    else:
        raise TypeError("Called printAst on a non-AST object")
    render(stack(doc, ''), file)


def _printStr(s):
    """Function checks argument for None before printing
    Useful as a default printing function parameter
    
    s: None or an object suitable to pass to print directly"""
    if s is not None:
        print s,

def _printFlat(irtype, children, childprint = _printStr, 
                       separator = None, prequel = None, sequel = None):
    """Prints an IR node and its children 'flatly'

    irtype: printable object denoting the IR type
    children: list of children to print
    childprint: function to invoke to print each child
    separator: optional printable separator between children
    prequel: parameterless function to invoke before printing children
    sequel: " " " " after " " """
    print '(' + irtype,
    if prequel is not None:
        prequel()
    for c in children[:-1]:
        childprint(c)
        _printStr(separator)
    childprint(children[-1])
    if sequel is not None:
        print #newline
        sequel()
        print
    print ')',

def _printNested(irtype, children, childprint = _printStr, 
                  prequel = None, separator = None, sequel = None):
    """Prints an IR node and its children using nesting 
    (intended to somewhat replicate scopes)

    irtype: pretty-printable object denoting the IR type
    children: list of children to print
    childprint: function to invoke to print each child
    separator: optional printable separator between children
    prequel: parameterless function to invoke before printing children
    sequel: " " " " after " " """

    print '(' + irtype
    if prequel is not None:
        prequel()
#    _indentation = _indentation + 1
    for c in children[:-1]:
        childprint(c)
        _printStr(separator),
    childprint(children[-1])
    if sequel is not None:
        print
        sequel()
#    _indentation = _indentation - 1
    print ')'

def printExpression(expr):
    """Returns a pretty-printable object for an expression IR node

    expr: Expression node in the AST"""
    if isinstance(expr, VariableExpr):
        varname = abut(expr.variable.name, expr.variable.identifier)
        return parens(space('VAR', varname))
    elif isinstance(expr, LiteralExpr):
        return parens(space('LIT', expr.literal))
    elif isinstance(expr, UnaryExpr):
        exprdoc = printExpressoin(expr.argument)
        return parens(space(['UEXPR', expr.operator.display, exprdoc]))
    elif isinstance(expr, BinaryExpr):
        exprdoclist = ['BEXPR',
                       printExpression(expr.left), 
                       expr.operator.display, 
                       printExpression(expr.right)]
        return parens(space(exprdoclist))
    elif isinstance(expr, IfExpr):
        thendoc = nest(printExpression(expr.ifTrue), 2)
        elsedoc = nest(printExpression(expr.ifFalse), 2)
        stacklist = [ linewr('IF', 4, printExpression(expr.argument)),
                      thendoc,
                      'ELSE',
                      elsedoc,
                      'ENDIF' ]
        return parens(stack(stacklist))
    elif isinstance(expr, ListCompExpr):
        return parensStack('LISTCOMP', nest(printIterator(expr.iterator), 2))
    elif isinstance(expr, GeneratorExpr):
        return paresStack('GENERATOR', nest(printIterator(expr.iterator), 2))
    elif isinstance(expr, CallExpr):
        arglist = punctuate(',', [printExpression(e) for e in expr.arguments])
        hungarg = None
        for init in arglist[:1]:
            hungarg = init
            for a in arglist[1:]:
                hungarg = linewr(hungarg, a, 0)
        return parens(space(['CALL', 
                             printExpression(expr.operator), 
                             brackets(hungarg)]))
    elif isinstance(expr, LetExpr):
        nextLet = None
        if expr.body is not None:
            nextLet = printExpression(expr.body)
        assigndoc = space(['LET', printParam(expr.name), '='])
        exprdoc = parens(linewr(assigndoc, printExpression(expr.rhs), 4))
        if expr.body is not None:
            exprdoc = abut(exprdoc, '...')
        return stack(exprdoc, nextLet) 
    elif isinstance(expr, LetrecExpr):
        defdoclist = [nest(printFuncDef(f), 2) for f in expr.definitions]
        return bracesStack(['LETREC'] + defdoclist + 
                               [nest(printExpression(expr.body), 2)])
    elif isinstance(expr, FunExpr):
        return brackets(linewr('LAMBDA', printFunction(expr.function)))
    elif isinstance(expr, ReturnExpr):
        return parens(space('RETURN', printExpression(expr.argument)))
    else:
        raise TypeError('Called printExpression on an unknown expression type')

def printIterator(iter):
    """Returns a pretty-printable object for an Iterator node in the AST

    iter: Iterator to be printed"""
    if isinstance(iter, ForIter):
        declclause = linewr(space(['FOR', printParam(iter.parameter), 'IN']), 
                          printExpression(iter.argument), 4)
        bodynest = nest(printIterator(iter.body), 2)
        return parenStack(declclause, bodynest)
    elif isinstance(iter, IfIter):
        return parenStack(linewr('GUARDIF', printExpression(iter.guard), 4),
                            nest(printIterator(iter.body)))
    elif isinstance(iter, DoIter):
        parenStack('DO', nest(printExpression(iter.body)))
    else:
        raise TypeError('Called printIterator on an unknown iterator type')


def printFuncDef(fdef):
    """Returns a pretty-printable object for a FunctionDef node in the AST

    fdef: FunctionDef to be printed"""
    return parens(linewr( space('DEF', printVar(fdef.name)), 
                        printFunction(fdef.function), 4))

def printFunction(f):
    """Returns a pretty-printable object for a Function node in the AST

    f: Function to be printed"""
    paramsdoc = []
    for p in f.parameters:
        paramsdoc.append(printParam(p))
    paramsdoc = brackets(abut(punctuate(',', paramsdoc)))
    fdoc = space('FUNCTION', paramsdoc)
    return parens(linewr(fdoc, printExpression(f.body)))

def printVar(v):
    """Returns a pretty-printable object for a variable in the AST
    v: Variable to be printed"""
    return abut(v.name, v.identifier)

def printParam(p):
    """Returns a pretty-printable object for a parameter in the AST
    TupleParams untested as of yet...
    p: Parameter to be printed"""
    if isinstance(p, VariableParam):
        printlist = []
        if p.annotation is not None:
            pass #Unimplemented?
        printlist.append(printVar(p.name))
        if p.default is not None:
            printlist.append(space('=', printVar(p.default)))
        return space(printlist)
    elif isinstance(p, TupleParam):
        return braces( space([printParam(f) for f in p.fields]))
    else:
        raise TypeError('Called printParam with unknown param type')

def printModule(m):
    """Returns a pretty-printable object for a Module in the AST
    As of yet untested.
    m: Module to be printed"""
    defdoclist = []
    for df in m.definitions:
        defdoclist = defdoclist + [printFuncDef(d) for d in dg]
    return bracesStack(['MODULE'] + defdoclist + 'END MODULE')

