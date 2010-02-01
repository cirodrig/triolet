# This tests type class inference when superclasses are involved.
# The type of f is:
#  forall a. Eq a => (a, a) * (a, a) -> bool

def f(a, b):
	u, v = a
	x, y = b
	u == y
	return a == b
