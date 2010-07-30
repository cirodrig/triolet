
def divmod(x, y):
	return (x // y, x % y)

def foo(xs, ys):
	return [d + r for (d, r) in (divmod(x, y) for x in xs for y in ys)]
