"""SSA generation module for the Pyon AST"""

import ast
from ast.parser_ast import *

#Stack of "join nodes": repositories for phi nodes


_savedForks = []
_joinNodeStack = [{}]
_joinNodeList = []

def _makeSSA(paramorfunc):
    #Taking advantage of the fact that both parameters and 
    # functions reference their corresponding variable object 
    # with the attribute 'name', even though they do not share 
    # it from a common inheritence heirarchy
    var = paramorfunc.name

    if hasattr(var, 'ssaver'):
        oldssaver = var.ssaver
        var.ssaver = var.topssaver+1
        var.topssaver = var.ssaver
    else:
        oldssaver = 0
        var.ssaver = 0
        var.topssaver = 0

    if var in _joinNodeStack[-1]:
        current, orig = _joinNodeStack[-1][var]
        _joinNodeStack[-1][var] = (var.ssaver, orig)
    else:
        _joinNodeStack[-1][var] = (var.ssaver, -1)

    paramorfunc.ssaver = var.ssaver

def _enterFork(joinNode):
    _joinNodeStack.append({})
    _joinNodeList.append(joinNode)

def _joinFork():
    phiNodes = []
    for var in set(_joinNodeStack[-1].keys()) | set(_savedForks[-1].keys()):
        forkone = -1
        forktwo = -1
        if var in _joinNodeStack[-1].keys():
            forktwo , _ = _joinNodeStack[-1][var]
        if var in _savedForks[-1].keys():
            forkone , _ = _savedForks[-1][var]
        #Create a new SSA version for every assigned variable
        var.ssaver = var.topssaver+1
        var.topssaver = var.ssaver
        
        phiNodes.append( (var, var.ssaver, forkone, forktwo) )

        orig = -1
        if var in _joinNodeStack[-2]:
            _, orig = _joinNodeStack[-2][var]
        _joinNodeStack[-2][var] = (var.ssaver, orig)
    _joinNodeStack.pop()
    _savedForks.pop()
    if len(phiNodes) > 0:
        _joinNodeList[-1].phiNodes = phiNodes

def _nextFork():
    _savedForks.append(_joinNodeStack[-1])

def _doIter(iter):
    if isinstance(iter, ForIter):
        #Need to fork SSA at this point
        _doExpr(iter.argument)
        _doIter(iter.body)
    elif isinstance(iter, IfIter):
        _doExpr(guard)
    elif isinstance(iter, DoIter):
        #Huh?  Seems like the body really ought to be a statement (list?)
        #_doExpr(iter.body)
        pass
    else:
        raise TypeError, type(iter)

def _doExpr(expr):
    if isinstance(expr, BinaryExpr):
        _doExpr(expr.left)
        _doExpr(expr.right)
    elif isinstance(expr, VariableExpr):
        expr.ssaver = expr.variable.ssaver
    elif isinstance(expr, LiteralExpr):
        pass #Nothing to do
    elif isinstance(expr, UnaryExpr):
        _doExpr(expr.argument)
    elif isinstance(expr, CallExpr):
        _doExpr(expr.operator)
        [_doExpr(a) for a in expr.arguments]
    elif isinstance(expr, ListCompExpr):
        _doIter(expr.iterator)
    elif isinstance(expr, GeneratorExpr):
        #Should this be treated differently than ListComp?
        _doIter(expr.iterator)
    elif isinstance(expr, CondExpr):
        #Conditional expressions actually can't contain any local 
        # definitions, so this is a trivial case
        _doExpr(expr.argument)
        _doExpr(expr.ifTrue)
        _doExpr(expr.ifFalse)
    elif isinstance(expr, LambdaExpr):
        #parameters should have gotten different variables
        _doExpr(expr.body)
    else:
        raise TypeError, type(expr)


def _doStmt(stmt):
    if isinstance(stmt, ExprStmt):
        _doExpr(stmt.expression)
    elif isinstance(stmt, ReturnStmt):
        _doExpr(stmt.expression)
    elif isinstance(stmt, AssignStmt):
        _doExpr(stmt.expression)
        _makeSSA(stmt.lhs)
    elif isinstance(stmt, IfStmt):
        #Same issues here as with CondExpr: need to fork and rejoin SSA paths
        _doExpr(stmt.cond)
        _enterFork(stmt)
        for s in stmt.ifTrue:
            _doStmt(s)
        _nextFork()
        for s in stmt.ifFalse:
            _doStmt(s)
        _joinFork()
    elif isinstance(stmt, DefGroupStmt):
        for d in stmt.definitions:
            #I remember something about doing SSA on functions 
            # at their declaration.  Is this all there is?
            _doFunction(d)
    else:
        raise TypeError, type(stmt)

def _doFunction(f):
    """Perform SSA for the parameters and body of a function
    NOTE: this function assumes that the caller has performed 
    SSA on the function name variable already"""
    _makeSSA(f)
    for p in f.parameters:
        _makeSSA(p)
    for s in f.body:
        _doStmt(s)
    


