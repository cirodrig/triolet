# This test case tests polymorphic container traversal.
# The function is called at both a list type and a stream type.  To compile
# it, we have to produce a function that works both in stream and imperative
# form.

def polymorphic_increment(collection):
	return map(lambda x: x + 1, collection)

def test_polymorphic_increment(xs : list(int)):
	return [x for x in polymorphic_increment(x for x in polymorphic_increment(xs))]
