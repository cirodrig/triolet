# Test the ability to convert functions between monomorphic and polymorphic
# types.  Pyon will insert type conversions before or after calls and
# generate wrapper functions at call sites.

def apply2(f, x, y):
	return f(x, y)

def mono_to_poly2(f, x, y : int):
	return apply2(f, x, y)

def mono(x : int):
	def difference_squared(x, y):
		d = x - y
		return d * d

	return mono_to_poly2(difference_squared, 10, 10)
