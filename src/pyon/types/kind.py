"""
Kinds (types of types).
"""

import pyon.pretty as pretty

class Kind(object):
    def __init__(self):
        raise NotImplementedError, "'Kind' is an abstract base class"

    def __eq__(self, other):
        raise NotImplementedError, "'Kind' is an abstract base class"

    def pretty(self):
        raise NotImplementedError, "'Kind' is an abstract base class"

class Star(Kind):
    "The kind that all types inhabit."

    _instance = None
    def __new__(cls):
        # Singleton class
        if not Star._instance:
            Star._instance = super(Star, cls).__new__(cls)
        return Star._instance

    def __init__(self): pass

    def __eq__(self, other):
        return self is other

    def __ne__(self, other):
        return self is not other

    def pretty(self):
        "k.pretty() -> pretty-printable object"
        return "*"

class Arrow(Kind):
    """
    An arrow kind Arrow(k1, k2) is the kind of a type constructor that
    maps a parameter in k1 to a result in k2.
    """

    def __init__(self, domain, range):
        assert isinstance(domain, Kind)
        assert isinstance(range, Kind)
        self.domain = domain
        self.range = range

    def __eq__(self, other):
        if not isinstance(other, Arrow): return False
        return self.domain == other.domain and self.range == other.range

    def __ne__(self, other):
        if not isinstance(other, Arrow): return True
        return self.domain != other.domain or self.range != other.range

    def pretty(self):
        "k.pretty() -> pretty-printable object"
        d = self.domain.pretty()
        if self.domain != Star(): d = pretty.parens(d)
        r = self.range.pretty()
        return pretty.space([d, "->", r])

def functionKind(num_parameters):
    """functionKind(int) -> kind

    Create the kind of an N-parameter type constructor where each parameter
    has kind '*'.
    """
    star = Star()
    k = star
    for n in range(num_parameters): k = Arrow(star, k)
    return k
