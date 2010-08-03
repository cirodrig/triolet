# Test variable capture

def app(fun : int -> int, arg : int): return fun(arg)

def test(g : int * int -> int, n : int):
	# This function captures 'g' and 'n'
	def f(m): return g(n, m)
	return app(f, 13)

def foo():
	def h(x : int, y : int): return x + y - 1
	return test(h, 8) - test(h, 21)


