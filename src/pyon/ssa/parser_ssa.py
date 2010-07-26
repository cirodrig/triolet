"""
SSA generation module for the Pyon Parser AST.

The entry point for SSA generation, @convertSSA, converts a Module to SSA form.
The following things are true of the output: 

* Every suite of statements contains exactly one control flow statement, at
  the end.
* Every control flow join point is labeled with a PhiNode object.  The control
  flow out of a function is annotated onto the Function.  The control
  flow out of an if-else is annotated onto the IfStmt.
* Every definition of a variable is annotated with an SSA ID.  Variables are
  defined by Function and VariableParam objects.
* Every use of a variable is annotated with an SSA ID, unless that variable
  is not tracked by SSA.  VariableExpr objects are variable uses.

Variables are tracked by SSA if they do not have an associated ANFVariable.
"""

import pyon.ast.parser_ast as ast 

class _NotSSA(object):
    """The single instance of this class is used in place of the SSA version
    for variables that do not have SSA versions."""
    pass

notSSA = _NotSSA()

class FallStmt(ast.Statement):
    """A statement representing the transfer of control flow 
    to another statement within the function"""
    def __init__(self, source_pos, join):
        assert isinstance(join, JoinNode)
        self.sourcePos = source_pos
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
            assert isinstance(stmt, (FallStmt, ast.ReturnStmt))
            assert isinstance(ver, int)
        self.ssaVersion = ssaver
        self.paths = paths

    def getVersion(self, var, stmt):
        """
        Look up the SSA version of @var that flows along the path from
        @stmt into this phi node.  The statment should be a fallthrough or
        return statement.

        This should only be called after SSA is completely constructed.
        """
        for phi_stmt, version in self.paths:
            if phi_stmt is stmt: return version

        # Error, not found
        raise KeyError, "Missing SSA information for a control flow path"

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

    def addPhi(self, var, stmt, version, alternate_fallthroughs = []):
        """    alternate_fallthroughs is a list of other fallthrough statements reaching this 
        join node for which variable definitionas have already been incorporated into 
        the current join's phi nodes.  If no phi node for that variable currently exists, 
        the definition of the variable live on the current fork's entry will be recorded 
        for every already-explored path. """ 
        if var in self.phiNodes:
            self.phiNodes[var].paths.append( (stmt, version) )
        else:
            _nextVarSSA(var)
            self.phiNodes[var] = PhiNode(var._ssaver, [(stmt, version)])

            #Retroactively create fallthough defintions for already-explored paths
            for alt_stmt in alternate_fallthroughs:
                # Assumes addPhi will only be called on variables present in _pathDefs
                assert (var in self._pathDefs)
                _ , origVersion = self._pathDefs[var] 
                self.phiNodes[var].paths.insert(-1, (alt_stmt, origVersion))
            

class IfNode(JoinNode):
    """Represents the control-flow join of an if or if-else 
    construct"""
    def __init__(self, join_stmt):
        JoinNode.__init__(self)
        self.hasret = False
        self.hasft = 0
        self.joinStmt = join_stmt

class ReturnNode(JoinNode):
    """Represents the control-flow join from exiting a function 
    and returning to the calling context"""
    pass

#The static counter of join nodes
JoinNode.enum = 0

def convertSSA(obj):
    "Convert a parser object into SSA format"
    if isinstance(obj, ast.Module):
        for f_list in obj.definitions:
            _doDefGroup(f_list)
        for exp in obj.exports:
            _doExport(exp)
    elif isinstance(obj, ast.Expression):
        _doExpr(obj)
    else:
        raise TypeError, type(obj)


# The stack of join nodes being visited by SSA analysis.  The join nodes 
# on this stack represent nested control dependence.
_joinNodeStack = [JoinNode()]

def _nextVarSSA(var):
    """returns the current SSA version number for this variable, and 
    adjusts the variable to the next SSA version available"""
    if hasattr(var, '_ssaver'):
        oldssaver = var._ssaver
        var._ssaver = var._topssaver+1
        var._topssaver = var._ssaver
    else:
        # If the variable is already associated with an ANF variable, it can't
        # be redefined
        if var.hasANFDefinition():
            raise RuntimeError, "Found definition of a non-SSA variable"
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
        for param in paramorfunc.fields: _makeSSA(param)
    else:
    #Taking advantage of the fact that both parameters and 
    # functions reference their corresponding variable object 
    # with the attribute 'name', even though they do not share 
    # it from a common inheritence heirarchy
        var = paramorfunc.name
        oldssaver = _nextVarSSA(var)
        paramorfunc.ssaver = var._ssaver

        _updatePathDef(var, var._ssaver, oldssaver)

def _killSSA(paramorfunc):
    """Kills variables that were defined using makeSSA.  The variables may
    not be referenced again.  This is used to record that a variable
    has gone out of scope, so that phi nodes are not generated for it."""
    if isinstance(paramorfunc, ast.TupleParam):
        for param in paramorfunc.fields: _killSSA(param)
    else:
        var = paramorfunc.name
        pathdefs = _joinNodeStack[-1]._pathDefs
        del pathdefs[var]


def _initPath(join):
    """Setup internal structures for entering a new control-flow path.
    join is the join node where the new path will need to record its 
    SSA dataflow into phi nodes"""
    _joinNodeStack.append(join)
    #join._pathDefs = {}

def _terminatePath():
    """Cease exploring the current path, without recording any further 
    dataflow.  Resets variables to their pre-path SSA versions in their 
    own structures and in the join node's pathdefs dictionary"""
    pathdefs = _joinNodeStack[-1]._pathDefs
    _joinNodeStack.pop()
    # Restore variables to their version live at path entry
    for var in pathdefs.keys():
        _ , var._ssaver = pathdefs[var]
        pathdefs[var] = (var._ssaver, var._ssaver)

def _recordPhis(fallthrough, alternate_fallthroughs = []):
    """Record the definitions of the path currently being explored into 
    the phi nodes of the join node provided to the corresponding _initPath
    invocation.  fallthough is recorded as the statement where this 
    path ends and control and dataflow merges with the join node"""
    joinNode = _joinNodeStack[-1]
    pathdefs = joinNode._pathDefs
    for var, (flow_ver, orig) in pathdefs.iteritems():
        #flow_ver, _ = _joinNodeStack[-1][var]
        #Add phi nodes for each path it was assigned from
        joinNode.addPhi(var, fallthrough, flow_ver, alternate_fallthroughs) 

def _finishPath(fallthrough, alternate_fallthroughs = []):
    """Terminate current path exploration, and register defintions as 
    assignments reaching the join block of statements, through phi nodes.  

    alternate_fallthroughs is a list of other fallthrough statements reaching this 
    join node for which variable definitionas have already been incorporated into 
    the current join's phi nodes.  If no phi node for that variable currently exists, 
    the definition of the variable live on the current fork's entry will be recorded 
    for every already-explored path.  
    """
    joinNode = _joinNodeStack[-1]
    _recordPhis(fallthrough, alternate_fallthroughs)
    _terminatePath()
    #A phi node generates a new SSA assignment, which should be 
    #  recorded in the previous fork nest, and as the variable's current
    #  ssa version
    for var, phi in joinNode.phiNodes.iteritems():
        _updatePathDef(var, phi.ssaVersion, -1)
        var._ssaver = phi.ssaVersion

def _nextPath(firstPathFallthrough, alternate_fallthroughs = []):
    """Begin recording a new path beginning from the same point as the 
    path currently being explored.  
    
    @alternate_fallthroughs is a list of other fallthrough statements reaching this 
    join node for which variable definitionas have already been incorporated into 
    the current join's phi nodes.  If no phi node for that variable currently exists, 
    the definition of the variable live on the current fork's entry will be recorded 
    for every already-explored path.  
    """
    join = _joinNodeStack[-1]
    _recordPhis(firstPathFallthrough, alternate_fallthroughs)
    _terminatePath()
    _initPath(join)

def _doIter(iter):
    """Perform SSA evaluation on an iterator"""
    if isinstance(iter, ast.ForIter):
        _doExpr(iter.argument)
        _makeSSA(iter.parameter)
        _doIter(iter.body)
        _killSSA(iter.parameter)
    elif isinstance(iter, ast.IfIter):
        _doExpr(iter.guard)
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
        v = expr.variable
        if v.hasANFDefinition(): expr.ssaver = notSSA
        else: expr.ssaver = v._ssaver
    elif isinstance(expr, ast.LiteralExpr):
        pass #Nothing to do
    elif isinstance(expr, ast.UnaryExpr):
        _doExpr(expr.argument)
    elif isinstance(expr, ast.CallExpr):
        _doExpr(expr.operator)
        for a in expr.arguments: _doExpr(a)
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
        # Assign each parameter
        for p in expr.parameters: _makeSSA(p)
        _doExpr(expr.body)
    elif isinstance(expr, ast.TupleExpr):
        for ex in expr.arguments: _doExpr(ex)
    else:
        raise TypeError, type(expr)

def _separateReturns(fn_ctx, stmtlist):
    """
    Find all 'return' statements in stmtlist and split them into an assignment
    of a temporary variable and a return statement.

    By performing this change, we ensure that the parameter of a return
    statement is always a simple variable.  This is assumed by later steps
    of SSA.
    """
    _, var = fn_ctx
    for i in reversed(range(len(stmtlist))):
        s = stmtlist[i]
        if isinstance(s, ast.ReturnStmt):
            retparam = ast.VariableParam(var)
            newretexpr = ast.VariableExpr(s.sourcePos, var)

            retcopy = ast.AssignStmt(s.sourcePos, retparam, s.expression)
            s.expression = newretexpr
            stmtlist.insert(i, retcopy)

def _regularizeControl(stmts, fallthrough):
    """
    Restructure a statement list so that the list has exactly one control flow
    transfer statement, at the end of the list.  If one needs to be inserted,
    insert @fallthrough.
    """
    for i in range(len(stmts)):
        if isinstance(stmts[i], (ast.ReturnStmt, FallStmt)):
            del stmts[i+1:]
            break
    else:
        stmts.append(fallthrough)

def _doStmtList(fn_ctx, stmts):
    """
    Perform SSA evaluation on a list of statements.

    fn_ctx : (Function, PythonVariable)
      The current function context.  It includes the current function and
      a variable representing the function's return value.
    stmts : [Statement]
      The list of statements to process.
    """
    # Bind all return statements to a single return variable
    _separateReturns(fn_ctx, stmts)

    # Pass the successor of each statement to doStmt, so that control flow
    # join points can be marked.
    # Detect whether any statements contain escaping control flow.
    hasret = False
    hasft = 1
    for s, next_s in zip(stmts, stmts[1:] + [None]):
        this_hasret, hasft = _doStmt(fn_ctx, s, next_s)
        hasret = hasret or this_hasret

    return (hasret, hasft)

def _doStmt(fn_ctx, stmt, next_stmt):
    """
    Perform SSA evaluation on a statement.  The second argument is 
    used only to mark if a return statement is seen in the subtree of the 
    particular statement.

    Return the control flow behavior of the statement: whether it has any
    escaping control flow, and the number of fallthrough paths it has (zero,
    one, or many).
    """
    if isinstance(stmt, ast.ExprStmt):
        _doExpr(stmt.expression)
        return (False, 1)

    elif isinstance(stmt, ast.ReturnStmt):
        _doExpr(stmt.expression)
        fdef, var = fn_ctx
        stmt.joinNode = fdef.joinPoint
        stmt.joinNode.addPhi(var, stmt, stmt.expression.ssaver)
        return (True, 0)

    elif isinstance(stmt, ast.AssignStmt):
        _doExpr(stmt.expression)
        _makeSSA(stmt.lhs)
        return (False, 1)

    elif isinstance(stmt, ast.IfStmt):
        assert next_stmt is not None
        #Expression evaluation happens first
        _doExpr(stmt.cond)
        reconverge = IfNode(next_stmt)
        stmt.joinPoint = reconverge

        #set up new control flow fork in the SSA structures
        _initPath(reconverge)
        truefall = FallStmt(stmt.sourcePos, reconverge)
        _regularizeControl(stmt.ifTrue, truefall)
        hasret1, hasft1 = _doStmtList(fn_ctx, stmt.ifTrue)

        #Wrap up the true path and switch to the other 
        _nextPath(truefall)
        falsefall = FallStmt(stmt.sourcePos, reconverge)
        _regularizeControl(stmt.ifFalse, falsefall)
        hasret2, hasft2 = _doStmtList(fn_ctx, stmt.ifFalse)

        _finishPath(falsefall, [truefall])

        hasret = reconverge.hasret = hasret1 or hasret2
        hasft = reconverge.hasft = min(2, hasft1 + hasft2)
        return (hasret, hasft)

    elif isinstance(stmt, ast.DefGroupStmt):
        _doDefGroup(stmt.definitions)
        return (False, 1)

    elif isinstance(stmt, FallStmt):
        return (False, 1)

    else:
        raise TypeError, type(stmt)

def _doFunction(f):
    """Perform SSA for the parameters and body of a function"""
    assert isinstance(f, ast.Function)
    f.joinPoint = ReturnNode()
    retvar = ast.PythonVariable('fret')
    fn_ctx = (f, retvar)

    # Need to insulate code containing the function definition from 
    # variable definitions inside the function 
    _joinNodeStack.append(JoinNode())
    for p in f.parameters: _makeSSA(p)
    _regularizeControl(f.body,
                       ast.ReturnStmt(f.sourcePos,
                                      ast.LiteralExpr(f.sourcePos, None)))
    _doStmtList(fn_ctx, f.body)
    _joinNodeStack.pop()

def _doDefGroup(f_list):
    """Perform SSA on a definition group."""
    # Define all functions
    for f in f_list: _makeSSA(f)

    # Do SSA on the bodies of all functions
    for f in f_list: _doFunction(f)

def _doExport(export):
    """Perform SSA on an export statement."""
    v = export.name

    # Only variables defined at the top level of this module may be exported.
    # This checks whether the variable was defined in the current module.
    if v.hasANFDefinition():
        raise RuntimeError, "Cannot export '" + v.name + "'; it is not defined in the current module"

    export.ssaver = v._ssaver
    return
