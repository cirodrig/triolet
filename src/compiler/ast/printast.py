# printast.py
#
# Prints the AST in human-readable form

from ast import *
import operators

#_indentation = 0

def printAst(root):
    """A generic, recursive printing function.
    Examines the argument type and calls the appropriate print function.

    root: an AST node marking the subtree to be printed"""
#    _indentation = 0
    if isinstance(root, Expression):
        printExpression(root)
    elif isinstance(root, Iterator):
        printIterator(root)
    elif isinstance(root, FunctionDef):
        printFuncDef(root)
    elif isinstance(root, Function):
        printFunction(root)
    elif isinstance(root, Variable):
        printVar(root)
    elif isinstance(root, Parameter):
        printParam(root)
    elif isinstance(root, Module):
        printModule(root)
    else:
        raise TypeError("Called printAst on a non-AST object")

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

    irtype: printable object denoting the IR type
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
    """Prints an expression IR node

    expr: Expression node in the AST"""
    if isinstance(expr, VariableExpr):
        _printFlat('VAR', [expr.variable.name , expr.variable.identifier])
    elif isinstance(expr, LiteralExpr):
        _printFlat('LIT', [expr.literal])
    elif isinstance(expr, UnaryExpr):
        _printFlat('UEXPR' + expr.operator.display, 
        		[expr.argument], printExpression)
    elif isinstance(expr, BinaryExpr):
        _printFlat('BEXPR', [expr.left, expr.right], 
                            printExpression, expr.operator.display)
    elif isinstance(expr, IfExpr):
        printNested('IF', [expr.ifTrue, expr.ifFalse], printExpression, 
        		separator = 'ELSE', 
        		prequel = lambda : printExpression(expr.argument) )
    elif isinstance(expr, ListCompExpr):
        printNested('LISTCOMP', [expr.iterator], printIterator)
    elif isinstance(expr, GeneratorExpr):
        printNested('GENERATOR', [expr.iterator], printIterator)
    elif isinstance(expr, CallExpr):
        _printFlat('CALL', expr.arguments, printExpression, 
                      prequel = lambda : printExpression(expr.operator))
    elif isinstance(expr, LetExpr):
        _printFlat('LET', [expr.rhs], printExpression, 
               prequel = lambda : printParam(expr.name) )
        if expr.body is not None:
            print '...'
            printExpression(expr.body)
    elif isinstance(expr, LetrecExpr):
        printNested('LETREC', expr.definitions, printFuncDef, 
                      sequel = lambda : printExpression(expr.body))
    elif isinstance(expr, FunExpr):
        _printFlat('LAMBDA', [expr.function], printFunction)
    elif isinstance(expr, ReturnExpr):
        _printFlat('RETURN', [expr.argument], printExpression)
    else:
        raise TypeError('Called printExpression on an unknown expression type')

def printIterator(iter):
    """Prints an Iterator node in the AST

    iter: Iterator to be printed"""
    if isinstance(iter, ForIter):
        printNested('FOR', [iter.argument], printExpression, 
                        prequel = lambda : printParam(iter.parameter),
                        sequel = lambda : printIterator(iter.body) )
    elif isinstance(iter, IfIter):
        printNested('GUARDIF', [iter.guard], printExpression,
                        sequel = lambda : printIterator(iter.body) )
    elif isinstance(iter, DoIter):
        printNested('DO', [iter.body], printExpression)
    else:
        raise TypeError('Called printIterator on an unknown iterator type')


def printFuncDef(fdef):
    """Prints a FunctionDef node in the AST

    fdef: FunctionDef to be printed"""
    _printFlat('FDEF', [fdef.function], printFunction, 
                  prequel = lambda : printVar(fdef.name))

def printFunction(f):
    """Prints a Function node in the AST

    f: Function to be printed"""
    _printFlat('FUNC', f.parameters, printParam, 
                    sequel = lambda : printExpression(f.body))

def printVar(v):
    """Prints a variable in the AST
    v: Variable to be printed"""
    print v.name, v.identifier,

def printParam(p):
    """Prints a parameter in the AST
    TupleParams untested as of yet...
    p: Parameter to be printed"""
    if isinstance(p, VariableParam):
        print '(',
        if p.annotation is not None:
            print p.annotation,
        printVar(p.name)
        if p.default is not None:
            print '=', p.default,
        print ')',
    elif isinstance(p, TupleParam):
        print '(',
        for field in p.fields:
            printParam(field)
        print ')',
    else:
        raise TypeError('Called printParam with unknown param type')

def printModule(m):
    """Prints a Module in the AST
    As of yet untested.
    m: Module to be printed"""
    print '(' 'MODULE'
    for df in m.definitions:
        for d in dg:
            printFuncDef(d)
    print 'END MODULE' ')'


