# This is an if-else where some variables are assigned on the first path and
# other variables are assigned on the second path.  This tests SSA's ability
# to properly compute the set of variables merged at a control flow join.
def f(x, y):
	w = 0
	z = 0
	if x > y:
		w = 2
	else:
		z = 2
	return w + z
