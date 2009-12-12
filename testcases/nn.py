
def dist(x, y):
    # Should be a built-in function
    pass

def reduce1(f, xs):
    # Should be a built-in function
    pass

def iota():
    # Should be a built-in function
    pass

def zip(xs, ys):
    # Should be a built-in function
    pass

def minIndex(f, xs):
    def pickMin(x, y):
        ix_x, val_x = x
	ix_y, val_y = y
	return x if val_x <= val_y else y

    ix, val = reduce1(pickMin, zip(iota(), xs))
    return ix

def nearestNeighbor(xs, ys):
    return [minIndex(dist(x, y) for y in ys) for x in xs]