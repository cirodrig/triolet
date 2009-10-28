
# This file contains some handwritten example AST code

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

xs_var = PythonVariable("xs")
ys_var = PythonVariable("ys")
x_var = PythonVariable("x")
y_var = PythonVariable("y")
nn_var = PythonVariable("nn")

# lambda x: dist(x,y)
nn_lambda = Function([VariableParam(x_var)],
                     CallExpr(VariableExpr(PythonVariable("dist")),
                              [VariableExpr(x_var), VariableExpr(y_var)]))

# [minIndex(lambda x: dist(x,y), ys) for x in xs]
nn_body = ForExpr(VariableParam(x_var),
                  VariableExpr(xs_var),
                  CallExpr(VariableExpr(PythonVariable("minIndex")),
                           [FunExpr(nn_lambda), VariableExpr(ys_var)]))

# def nn(xs, ys):
#     return [minIndex(lambda x: dist(x,y), ys) for x in xs]

nn = FunctionDef(nn_var,
                 Function([VariableParam(xs_var), VariableParam(ys_var)],
                          nn_body))

