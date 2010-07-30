# Test ability to compile floating-point math operators

def float_math(a,b,c,d):
	e = a + b + 1e-10
	f = c - d
	g = f / e
	h = -g ** 2.5
	return h
