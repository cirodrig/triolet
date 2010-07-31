# Test function parameters, indirect function calls, and lambdas

def pick(f : int -> int, g : int -> int, b):
	return f if b else g

def foo():
	return pick(lambda n: 500 + n, lambda n: 500 - n, False)(3)
