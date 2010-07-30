# Nested if-else statements, with some 'return' statements mixed in.

def test_ifelse(a,b):
	if a != 0:
		if b == 0:
			return (0, True)
		elif b > 0:
			c = b / a
			positive = True
		else:
			c = -b / a
			positive = False
		x = c
	else:
		return (0, True)

	return (c, positive)	
