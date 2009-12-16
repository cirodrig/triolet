"""SSA generation module for the Pyon Parser AST"""

import pyon.ast.parser_ast as ast 

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
            assert ( isinstance(stmt, FallStmt) 
                           or isinstance(stmt, ast.ReturnStmt) )
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
        self._pathDefs = {}
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


# The stack of join nodes being visited by SSA analysis.  The join nodes 
# on this stack represent nested control dependence.
_joinNodeStack = [JoinNode()]

# The stack of functions being visited by SSA analysis.  The current function
# is on the top of the stack.
# Each element is a (function, return-variable) pair, where return-variable
# is a new PythonVariable representing the function's return value.
_functionStack = []

def _nextVarSSA(var):
    """returns the current SSA version number for this variable, and 
    adjusts the variable to the next SSA version available"""
    if hasattr(var, '_ssaver'):
        oldssaver = var._ssaver
        var._ssaver = var._topssaver+1
        var._topssaver = var._ssaver
    else:
        oldssaver = -1 
        var._ssaver = 0
        var._topssaver = 0
    return oldssaver

def _updatePathDef(var, newver, oldver):
    """Updates the current path's lastest killing definition of var to
    newver.  If a value for the original version of the variable on path 
    entry is not recorded, oldver will be recorded as that value"""
    pathdefs = _joinNodeStack[-1]._pathDefs

    if var in pathdefs:
        _ , oldver = pathdefs[var]
    pathdefs[var] = (newver, oldver)

def _makeSSA(paramorfunc):
    "Converts a variable definition to SSA form"
    if isinstance(paramorfunc, ast.TupleParam):
        [_makeSSA(param) for param in paramorfunc.fields]
    else:
    #Taking advantage of the fact that both parameters and 
    # functions reference their corresponding variable object 
    # with the attribute 'name', even though they do not share 
    # it from a common inheritence heirarchy
        var = paramorfunc.name
        oldssaver = _nextVarSSA(var)
        pathdefs = _joinNodeStack[-1]._pathDefs
        paramorfunc.ssaver = var._ssaver

        _updatePathDef(var, var._ssaver, oldssaver)


def _initPath(join):
    """Setup internal structures for entering a new control-flow path.
    join is the join node where the new path will need to record its 
    SSA dataflow into phi nodes"""
    _joinNodeStack.append(join)
    join._pathDefs = {}

def _terminatePath():
    """Cease exploring the current path, without recording any further 
    dataflow.  Resets variables to their pre-path SSA versions"""
    pathdefs = _joinNodeStack[-1]._pathDefs
    _joinNodeStack.pop()
    # Restore variables to their version live at path entry
    for var in pathdefs.keys():
        _ , var._ssaver = pathdefs[var]

def _recordPhis(fallthrough):
    """Record the definitions of the path currently being explored into 
    the phi nodes of the join node provided to the corresponding _initPath
    invocation.  fallthough is recorded as the statement where this 
    path ends and control and dataflow merges with the join node"""
    joinNode = _joinNodeStack[-1]
    pathdefs = joinNode._pathDefs
    for var, (flow_ver, _) in pathdefs.iteritems():
        #flow_ver, _ = _joinNodeStack[-1][var]
        #Add phi nodes for each path it was assigned from
        joinNode.addPhi(var, fallthrough, flow_ver) 

def _finishPath(fallthrough, record):
    """Terminate current path exploration, and register phiNodes as 
    assignments reaching the join block of statements if boolean @record is 
    true"""
    joinNode = _joinNodeStack[-1]
    if record:
        _recordPhis(fallthrough)
    _terminatePath()
    #A phi node generates a new SSA assignment, which should be 
    #  recorded in the previous fork nest, and as the variable's current
    #  ssa version
    for var, phi in joinNode.phiNodes.iteritems():
        _updatePathDef(var, phi.ssaVersion, -1)
        var._ssaver = phi.ssaVersion

def _nextPath(firstPathFallthrough, record):
    """Begin recording a new path beginning from the same point as the 
    path currently being explored.  The current path's definitions 
    are recorded into phi nodes if the boolean @record is true"""
    join = _joinNodeStack[-1]
    if record:
        _recordPhis(firstPathFallthrough)
    _terminatePath()
    _initPath(join)

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
    """
    Find all 'return' statements in stmtlist and split them into an assignment
    of a temporary variable and a return statement.

    By performing this change, we ensure that the parameter of a return
    statement is always a simple variable.  This is assumed by later steps
    of SSA.
    """
    _, var = _functionStack[-1]
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

    # Bind all return statements to a single return variable
    _separateReturns(stmts)

    # Need to mark join nodes, after they are processed, with the 
    # statement immediately following them in the list (no parent pointer)
    join = None
    for s in stmts:
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
        _initPath(reconverge)
        _doStmtList(stmt.ifTrue, truefall)
        #Wrap up the true path and switch to the other 
        _nextPath(truefall, not isinstance(stmt.ifTrue[-1], ast.ReturnStmt))

        falsefall = FallStmt(reconverge)
        _doStmtList(stmt.ifFalse, falsefall)
        _finishPath(falsefall, 
                    not (len(stmt.ifFalse) == 0 
                       or isinstance(stmt.ifFalse[-1], ast.ReturnStmt) ) )

        #Collect return-node information
        ifhasret = truefall.hasret or falsefall.hasret
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
    _makeSSA(f)
    f.joinPoint = ReturnNode()
    retvar = ast.PythonVariable('fret')
    _functionStack.append((f, retvar))
    # Need to insulate code containing the function definition from 
    # variable definitions inside the function 
    _joinNodeStack.append(JoinNode())
    for p in f.parameters:
        _makeSSA(p)
    _doStmtList(f.body, ast.ReturnStmt(ast.LiteralExpr(None)))
    _joinNodeStack.pop()
    _functionStack.pop()


