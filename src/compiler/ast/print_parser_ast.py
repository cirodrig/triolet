"""
Pretty-print parser AST data structures.
"""

import sys

import ast
import operators
from parser_ast import *
import pretty

def prettyAst(obj):
    """Format a parser AST object as a pretty-printable object."""
    if isinstance(obj, Module):
        return _prModule(obj)
    elif isinstance(obj, Function):
        return _prFunction(obj)
    elif isinstance(obj, Statement):
        return _prStatement(obj)
    elif isinstance(obj, Iterator):
        return _prIterator(obj)
    elif isinstance(obj, Expression):
        return _prExpression(obj, _PREC_OUTER)
    elif isinstance(obj, Parameter):
        return _prParameter(obj)
    elif isinstance(obj, PythonVariable):
        return _prVariable(obj)
    else:
        raise TypeError, type(obj)
    
def printAst(obj, f = sys.stdout):
    """
    printAst(obj)       -- print to stdout
    printAst(obj, file) -- print to file

    Pretty-print an AST object."""
    doc = prettyAst(obj)
    pretty.render(pretty.stack(doc, ''), f)

###############################################################################
# Internal stuff

# Expression precedence, used for deciding whether to use parentheses

_PREC_OUTER = 0
_PREC_LAMBDA = 1
_PREC_COND = 2
_PREC_CALL = 10

def _tuple(items):
    return pretty.parens(
        pretty.space(
        pretty.punctuate(',', [prettyAst(i) for i in items])))

def _prVariable(v):
    return v.name

def _prParameter(p):
    if isinstance(p, VariableParam):
        return prettyAst(p.name)
    elif isinstance(p, TupleParam):
        return _tuple(p.fields)
    else:
        raise TypeError, type(p)

def _prExpression(e, precedence):
    """Print an expression in a context with the specified precedence.

    If the expression has precedence lower than or equal to the context,
    then the expression should be parenthesized."""

    # Use this function to put parentheses around the whole expression
    # if it might be needed
    def parenthesize(local_prec, doc):
        if local_prec <= precedence: return pretty.parens(doc)
        else: return doc

    if isinstance(e, VariableExpr):
        return prettyAst(e.variable)
    elif isinstance(e, LiteralExpr):
        lit = e.literal
        if lit is None:
            return "None"
        elif isinstance(lit, (int, float, bool)):
            return str(lit)
        else:
            raise TypeError, "Unexpected literal value"
    elif isinstance(e, BinaryExpr):
        prec = e.operator.precedence
        assoc = e.operator.associativity

        # Choose precedence context for subexpressions
        if assoc == operators.ASSOC_LEFT:
            left_prec = prec - 1
            right_prec = prec
        elif assoc == operators.ASSOC_RIGHT:
            left_prec = prec
            right_prec = prec - 1
        else:
            right_prec = left_prec = prec

        # Generate document 
        left = _prExpression(e.left, left_prec)
        right = _prExpression(e.right, right_prec)
        doc = pretty.space([left, e.operator.display, right])
        return parenthesize(prec, doc)
    elif isinstance(e, ListCompExpr):
        return pretty.brackets(prettyAst(e.iterator))
    elif isinstance(e, GeneratorExpr):
        return pretty.parens(prettyAst(e.iterator))
    elif isinstance(e, CallExpr):
        doc = pretty.abut(_prExpression(e.operator, _PREC_CALL),
                          _tuple(e.arguments))
        return parenthesize(_PREC_CALL, doc)
    elif isinstance(e, CondExpr):
        if_true = _prExpression(e.ifTrue, _PREC_COND)
        arg = _prExpression(e.argument, _PREC_COND)
        if_false = _prExpression(e.ifFalse, _PREC_COND)
        
        doc = pretty.space([if_true, 'if', arg, 'else', if_false])
        return parenthesize(_PREC_COND, doc)
    elif isinstance(e, LambdaExpr):
        parameter_list = pretty.space(
            pretty.punctuate(',', (prettyAst(p) for p in e.parameters)))
        doc = pretty.space(['lambda',
                            pretty.abut(parameter_list, ':'),
                            _prExpression(e.body, _PREC_LAMBDA)])
        return parenthesize(_PREC_LAMBDA, doc)
    else:
        raise TypeError, type(e)

def _prIterator(i):
    # When body is found, put it here
    body = None

    # List of iteration expressions
    iteration = []

    while True:
        if isinstance(i, ForIter):
            iteration.append(pretty.space(['for', prettyAst(i.parameter),
                                           'in', prettyAst(i.argument)]))
            i = i.body
            continue
        elif isinstance(i, IfIter):
            iteration.append(pretty.space('if', prettyAst(i.guard)))
            i = i.body
            continue
        elif isinstance(i, DoIter):
            body = prettyAst(i.body)
            break
        else:
            raise TypeError, type(i)

    return pretty.space(body, pretty.space(iteration))
        
def _prStatement(s):
    if isinstance(s, ExprStmt):
        return prettyAst(s.expression)
    elif isinstance(s, AssignStmt):
        return pretty.space([prettyAst(s.lhs), '=', prettyAst(s.expression)])
    elif isinstance(s, ReturnStmt):
        return pretty.space('return', prettyAst(s.expression))
    elif isinstance(s, IfStmt):
        #if COND:
        #    THEN
        #else:
        #    ELSE
        if_line = pretty.abut(pretty.space('if', prettyAst(s.cond)), ':')
        tr_suite = pretty.nest(pretty.stack(prettyAst(e) for e in s.ifTrue), 4)

        fa = s.ifFalse
        if fa:
            fa_suite = pretty.nest(pretty.stack(prettyAst(e) for e in fa), 4)
            fa_text = pretty.stack('else:', fa_suite)
        else:
            fa_text = None

        return pretty.stack([if_line, tr_suite, fa_text])
    elif isinstance(s, DefGroupStmt):
        return pretty.stack(_prFunction(f) for f in s.definitions)
    else:
        raise TypeError, type(s)

def _prFunction(f):
    param_list = _tuple(f.parameters)
    f_name = prettyAst(f.name)
    f_decl = pretty.abut(pretty.space('def', pretty.abut(f_name, param_list)),
                         ':')
    f_body = pretty.stack(prettyAst(s) for s in f.body)
    return pretty.stack(f_decl, pretty.nest(f_body, 4))

def _prModule(m):
    return pretty.stack(pretty.stack(_prFunction(f),'')
                        for f in m.iterDefinitions())
