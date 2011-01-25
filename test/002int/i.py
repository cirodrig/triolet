# Test ability to compile integer operators

export ccall "int_math" int_math : int * int * int * int -> int

def int_math(a : int, b : int, c : int, d : int):
	t1 = a * b
	t2 = c + 3
	t4 = t1 - d
	return t2 * t4

