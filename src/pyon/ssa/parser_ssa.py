"""SSA generation module for the Pyon Parser AST"""

import pyon.ast.parser_ast as ast 
#Stack of "join nodes": repositories for phi nodes



class FallStmt(ast.Statement):
    """A statement representing the transfer of control flow 
    to another statement within the function"""
    def __init__(self, join):
        assert isinstance(join, JoinNode)
        self.joinNode = join

class PhiNode(object):
    """Represents the variable-agnostic SSA information of a phiNode, 
    i.e. the ssa version defined by the phi node, and a list of 
    (statement, version) pairs that define the versions defined from 
    each path leading to the join.  An SSA version number of -1 indicates 
    that the variable is undefined when control returns from that path."""
    def __init__(self, ssaver, paths):
        assert isinstance(ssaver, int)
        for stmt, ver in paths:
            assert isinstance(stmt, FallStmt) or isinstance(stmt, ast.ReturnStmt)
            assert isinstance(ver, int)
        self.ssaVersion = ssaver
        self.paths = paths

class JoinNode(object):
    """An object representing a control-flow join, and containing the 
    phi nodes representing the dataflow through that join"""
    def __init__(self):
        self.num = JoinNode.enum
        JoinNode.enum = JoinNode.enum + 1
        self.phiNodes = {}
        #Structure is filled in lazily

    def setPhis(self, phis):
        for var, phiNode in phis.iteritems():
            assert isinstance(var, ast.Variable)
            assert isinstance(phiNode, PhiNode)
        self.phiNodes = phis

    def addPhi(self, var, stmt, version):
        if var in self.phiNodes:
            self.phiNodes[var].paths.append( (stmt, version) )
        else:
            _nextVarSSA(var)
            self.phiNodes[var] = PhiNode(var._ssaver, [(stmt, version)])
            

class IfNode(JoinNode):
    """Represents the control-flow join of an if or if-else 
    construct"""
    def __init__(self):
        JoinNode.__init__(self)
        self.hasret = False

    def setJoin(self, stmt):
        assert isinstance(stmt, ast.Statement)
        self.joinStmt = stmt

class ReturnNode(JoinNode):
    """Represents the control-flow join from exiting a function 
    and returning to the calling context"""
    pass

#The static counter of join nodes
JoinNode.enum = 0

def convertSSA(obj):
    "Convert a parser object into SSA format"
    if isinstance(obj, ast.Module):
        [[_doFunction(f) for f in f_list] for f_list in obj.definitions]
    elif isinstance(obj, ast.Function):
        _doFunction(obj)
    elif isinstance(obj, ast.Statement):
        _doStmt(obj, FallStmt(JoinNode()))
    elif isinstance(obj, ast.Expression):
        _doExpr(obj)
    elif isinstance(obj, ast.Parameter):
        pass
    elif isinstance(obj, ast.PythonVariable):
        pass
    else:
        raise TypeError, type(obj)

_savedForks = []
_phiNodeStack = [{}]
_functionStack = []
_returnVarCnt = 0

def _nextVarSSA(var):
    """returns the current SSA version number for this variable, and 
    adjusts the variable to the next SSA version available"""
    if hasattr(var, '_ssaver'):
        oldssaver = var._ssaver
        var._ssaver = var._topssaver+1
        var._topssaver = var._ssaver
    else:
        oldssaver = 0
        var._ssaver = 0
        var._topssaver = 0
    return oldssaver


def _makeSSA(paramorfunc):
    "Converts a variable definition to SSA form"
    #Taking advantage of the fact that both parameters and 
    # functions reference their corresponding variable object 
    # with the attribute 'name', even though they do not share 
    # it from a common inheritence heirarchy
    if isinstance(paramorfunc, ast.TupleParam):
        [_makeSSA(param) for param in paramorfunc.fields]
    else:
        var = paramorfunc.name
        oldssaver = _nextVarSSA(var)

        if var in _phiNodeStack[-1]:
            current, orig = _phiNodeStack[-1][var]
            _phiNodeStack[-1][var] = (var._ssaver, orig)
        else:
            _phiNodeStack[-1][var] = (var._ssaver, oldssaver)

        paramorfunc.ssaver = var._ssaver

def _enterLoop(phiNode):
    "Setup data structure for entering a looping structure"
    _enterFork()
    _nextFork()

def _enterFork():
    "Setup internal structures for entering a control flow fork"
    _phiNodeStack.append({})

def _joinFork(truefall, falsefall, joinNode, hasret):
    "Join the paths of control flow from the most recent fork"
    phiNodes = {} 
    joinNode.setPhis(phiNodes)
    for var in set(_phiNodeStack[-1].keys()) | set(_savedForks[-1].keys()):
        forkone = -1
        forktwo = -1
        if var in _phiNodeStack[-1].keys():
            forktwo , forkone = _phiNodeStack[-1][var]
        else: #var must be in _savedForks
            forkone , forktwo = _savedForks[-1][var]
        if var in _savedForks[-1].keys():
            forkone , orig = _savedForks[-1][var]
        else: #both forks have already been set correctly
            pass

        #Add phi nodes for each path it was assigned from
        if truefall is not None:
            joinNode.addPhi(var, truefall, forkone) 
        if falsefall is not None:
            joinNode.addPhi(var, falsefall, forktwo) 
        
        #A phi node generates a new SSA assignment, which should be 
        #  recorded in the previous fork nest (if any)
        orig = -1
        if var in _phiNodeStack[-2]:
            _, orig = _phiNodeStack[-2][var]
        _phiNodeStack[-2][var] = (var._ssaver, orig)

    _phiNodeStack.pop()
    _savedForks.pop()
    joinNode.hasret = hasret

def _nextFork():
    """Save state of the first path of a fork, and begin 
    recording the second path's state"""
    _savedForks.append(_phiNodeStack[-1])
    _phiNodeStack[-1] = {}
    for var in _savedForks[-1].keys():
        _ , var._ssaver = _savedForks[-1][var]

def _doIter(iter):
    """Perform SSA evaluation on an iterator"""
    if isinstance(iter, ast.ForIter):
        _doExpr(iter.argument)
        _makeSSA(iter.parameter)
        _doIter(iter.body)
    elif isinstance(iter, ast.IfIter):
        _doExpr(guard)
        _doIter(iter.body)
    elif isinstance(iter, ast.DoIter):
        _doExpr(iter.body)
    else:
        raise TypeError, type(iter)

def _doExpr(expr):
    """Perform SSA evaluation on an expression"""
    if isinstance(expr, ast.BinaryExpr):
        _doExpr(expr.left)
        _doExpr(expr.right)
    elif isinstance(expr, ast.VariableExpr):
        expr.ssaver = expr.variable._ssaver
    elif isinstance(expr, ast.LiteralExpr):
        pass #Nothing to do
    elif isinstance(expr, ast.UnaryExpr):
        _doExpr(expr.argument)
    elif isinstance(expr, ast.CallExpr):
        _doExpr(expr.operator)
        [_doExpr(a) for a in expr.arguments]
    elif isinstance(expr, ast.ListCompExpr):
        _doIter(expr.iterator)
    elif isinstance(expr, ast.GeneratorExpr):
        #Should this be treated differently than ListComp?
        _doIter(expr.iterator)
    elif isinstance(expr, ast.CondExpr):
        #Conditional expressions actually can't contain any local 
        # definitions, so this is a trivial case
        _doExpr(expr.argument)
        _doExpr(expr.ifTrue)
        _doExpr(expr.ifFalse)
    elif isinstance(expr, ast.LambdaExpr):
        #parameters should have gotten different variables
        _doExpr(expr.body)
    elif isinstance(expr, ast.TupleExpr):
        [_doExpr(ex) for ex in expr.arguments]
    else:
        raise TypeError, type(expr)

def _separateReturns(stmtlist):
    fdef, var = _functionStack[-1]
    global _returnVarCnt
    for i in reversed(range(len(stmtlist))):
        s = stmtlist[i]
        if isinstance(s, ast.ReturnStmt):
            retparam = ast.VariableParam(var)
            newretexpr = ast.VariableExpr(var)

            retcopy = ast.AssignStmt(retparam, s.expression)
            s.expression = newretexpr
            stmtlist.insert(i, retcopy)

def _doStmtList(stmts, fallthrough):
    """Perform SSA evaluation on a list of statements
    The second argument provides the fallthrough mechanism, which 
    is inserted if the statement list does not end in a return statement"""
    retval = None
    fallthrough.hasret = False
    if len(stmts) == 0 or not isinstance(stmts[-1], ast.ReturnStmt):
        stmts.append(fallthrough)
        retval = fallthrough
    _separateReturns(stmts)
    join = None
    for s in stmts:
        x, y = _functionStack[-1]
        if join is not None:
            join.setJoin(s)
        if isinstance(s, ast.ReturnStmt):
            fallthrough.hasret = True
        join = _doStmt(s, fallthrough)
    return retval

def _doStmt(stmt, listfallthrough):
    """Perform SSA evaluation on a statement.  The second argument is 
    used only to mark if a return statement is seen in the subtree of the 
    particular statement."""
    if isinstance(stmt, ast.ExprStmt):
        _doExpr(stmt.expression)
    elif isinstance(stmt, ast.ReturnStmt):
        _doExpr(stmt.expression)
        fdef, var = _functionStack[-1]
        stmt.joinNode = fdef.joinPoint
        stmt.joinNode.addPhi(var, stmt, stmt.expression.ssaver)
    elif isinstance(stmt, ast.AssignStmt):
        _doExpr(stmt.expression)
        _makeSSA(stmt.lhs)
    elif isinstance(stmt, ast.IfStmt):
        #Expression evaluation happens first
        _doExpr(stmt.cond)
        reconverge = IfNode()
        stmt.joinPoint = reconverge
        truefall = FallStmt(reconverge)
        #set up new control flow fork in the SSA structures
        _enterFork()
        _doStmtList(stmt.ifTrue, truefall)
        #switch to the other fork
        _nextFork()
        falsefall = FallStmt(reconverge)
        _doStmtList(stmt.ifFalse, falsefall)
        #merge the two forks into the join node
        ifhasret = truefall.hasret or falsefall.hasret
        if isinstance(stmt.ifTrue[-1], ast.ReturnStmt):
            truefall = None
        if len(stmt.ifFalse) == 0 or isinstance(stmt.ifFalse[-1], ast.ReturnStmt):
            falsefall = None
        _joinFork(truefall, falsefall, reconverge, ifhasret)
        listfallthrough.hasret = listfallthrough.hasret or ifhasret
        #following statement is recorded in the join node lazily
        return reconverge
    elif isinstance(stmt, ast.DefGroupStmt):
        for d in stmt.definitions:
            #I remember something about doing SSA on functions 
            # at their declaration.  Is this all there is?
            _doFunction(d)
    elif isinstance(stmt, FallStmt):
        pass
    else:
        raise TypeError, type(stmt)




def _doFunction(f):
    """Perform SSA for the parameters and body of a function"""
    assert isinstance(f, ast.Function)
    global _returnVarCnt
    _makeSSA(f)
    f.joinPoint = ReturnNode()
    retvar = ast.PythonVariable('fret', _returnVarCnt)
    _functionStack.append((f, retvar))
    _returnVarCnt = _returnVarCnt + 1
    for p in f.parameters:
        _makeSSA(p)
    _doStmtList(f.body, ast.ReturnStmt(ast.LiteralExpr(None)))
    _functionStack.pop()


