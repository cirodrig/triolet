# This test case causes ANF generation to create a 'letrec'
def equal3(x, y, z):
	if x == y:
		if y == z:
			return True
	return False
