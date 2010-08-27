# Test ability to compile integer operators

export ccall "int_math" int_math : int * int * int * int -> int

def int_math(a,b,c,d):
	return (a ^ b & c | d) // 2
