# Test the handling of monomorphic recursion

def fib(x):
	if x == 0: return 1
	elif x == 1: return 1
	else: return fib(x-1) + fib(x-2)
