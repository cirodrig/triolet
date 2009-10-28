
from ast import *

a_var = PythonVariable("a")
b_var = PythonVariable("b")
c_var = PythonVariable("c")
f_var = PythonVariable("f")

# def f(a, b):
#     c = a + b
#     return c

f = FunctionDef(f_var,
                Function([VariableParam(a_var), VariableParam(b_var)],
                         LetExpr(VariableParam(c_var),
                                 BinaryExpr(operators.ADD,
                                            VariableExpr(a_var),
                                            VariableExpr(b_var)),
                                 VariableExpr(c_var))))

