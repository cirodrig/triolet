
from ast import *

a_var = PythonVariable("a")
b_var = PythonVariable("b")
c_var = PythonVariable("c")
f_var = PythonVariable("f")

f = FunctionDef(f_var,
                Function([a_var, b_var],
                         LetExpr(exprDefault,
                                 c_var,
                                 BinaryExpr(exprDefault,
                                            operators.ADD, VariableExpr(exprDefault, a_var), VariableExpr(exprDefault, b_var)),
                                 VariableExpr(exprDefault,
                                              c_var))))

