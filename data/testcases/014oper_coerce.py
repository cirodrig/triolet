# This tests some unusual cases involving polymorphic function calls.
# Function "id" is called at two different types.  The result of the first
# call must be coerced to the right representation before it's called.

def id(x): return x

def pcall(n : int): return id(id)(n)
