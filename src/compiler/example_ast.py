
from ast import *

a_var = PythonVariable("a")
b_var = PythonVariable("b")
c_var = PythonVariable("c")
f_var = PythonVariable("f")

# def f(a, b):
#     c = a + b
#     c

f = FunctionDef(f_var,
                Function([a_var, b_var],
                         LetExpr(c_var,
                                 BinaryExpr(operators.ADD,
                                            VariableExpr(a_var),
                                            VariableExpr(b_var)),
                                 VariableExpr(c_var))))

