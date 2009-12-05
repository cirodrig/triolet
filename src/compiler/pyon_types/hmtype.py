"""
Hindley-Milner types with type classes.

Types are represented by the classes TyVar, FunTy, and TyConApp.  These are
immutable data types (except for mutation due to unification).
"""

import unification

class TyVar(unification.Variable):
    """
    A type variable.
    """

    def rename(self, mapping):
        # First, canonicalize the variable.
        v = self.canonicalize()

        # If this variable is a key in the mapping, then return its associated
        # value.  Otherwise, no change.
        try: return mapping[v]
        except KeyError: return v

class TyCon(object):
    """
    A type constructor.
    """

    def __init__(self):
        raise NotImplementedError, "'TyCon' is an abstract base class"
        self.numParams = None           # Number of parameters

class TupleTyCon(object):
    """
    A tuple type constructor.
    """

    def __init__(self, length):
        self.numParams = length

    def __eq__(self, other):
        self.numParams == other.numParams

class FunTyCon(object):
    """
    A function type constructor.
    """
    instance = None

    def __new__(cls):
        # This is a singleton class
        if cls.instance is None:
            return object.__new__(cls)
        else:
            return cls.instance

    def __init__(self):
        self.numParams = 2

    def __eq__(self, other):
        return True

class FunTy(unification.Term):
    """
    A function type.
    """

    def __init__(self, dom, rng):
        self.domain = dom
        self.range = rng

    def __eq__(self, other):
        return self.domain == other.domain and self.range == other.range

    def getConstructor(self):
        return FunTyCon()

    def getParameters(self):
        return [self.domain, self.range]

    def rename(self, mapping):
        """
        Apply a substitution to all type variables in this term.  A new
        type is returned.
        """
        return FunTy(self.domain.rename(), self.range.rename())

class TyConApp(unification.Term):
    """
    A type constructor application.
    """

    def __new__(cls, con, params):
        if con.numParams != len(params):
            raise ValueError, \
                  "Wrong number of parameters to type constructor application"

        # Function type constructors are are a different type
        if con is FunTyCon():
            return FunTy(params[0], params[1])
        else:
            return unification.Term.__new__(self, con, params)

    def __init__(self, con, params):
        self.constructor = con
        self.parameters = params

    def __eq__(self, other):
        if self.constructor != other.constructor:
            return False
        for p, q in zip(self.parameters, other.parameters):
            if p != q: return False
        return True

    def getConstructor(self):
        return self.constructor

    def getParameters(self):
        return self.parameters

    def rename(self, mapping):
        """
        Apply a substitution to all type variables in this term.  A new
        type is returned.
        """
        return TyConApp(self.constructor,
                        [p.rename(mapping) for p in self.parameters])

###############################################################################
    
class TyScheme(object):
    """
    A type scheme.
    """

    def __init__(self, qvars, t):
        self.qvars = qvars
        self.type = t

    def instantiate(self):
        """
        scheme.instantiate() -> type
        Instantiate a type scheme by creating fresh variables for each type.
        """
        # Rename each type variable to a fresh variable
        mapping = dict((v, TyVar()) for v in self.qvars)
        return self.type.rename(mapping)

def generalize(t):
    """
    Generalize a type by quantifying over all free type variables.
    """
    return TyScheme(list(freeVariables(t)), t)
