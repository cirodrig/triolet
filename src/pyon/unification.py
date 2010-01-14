"""
First-order unification.
"""

import pyon.pretty as pretty

class Unifiable(object):
    """Abstract base class of objects that can be unified."""

    def __init__(self):
        raise NotImplementedError, "'Unifiable' is an abstract base class"

    def canonicalize(self):
        """
        Get the canonical representation of this unifiable object.
        Only this object (not sub-objects) is canonicalized.
        """
        raise NotImplementedError

    def occursCheck(self, v):
        """
        x.occursCheck(v) -> bool
        Return true iff the unification variable 'v' is part of this
        unifiable object.
        """
        raise NotImplementedError

    def freeVariables(self):
        return addFreeVariables(self, set())

    def addFreeVariables(self, s):
        """
        x.addFreeVariables(s) -- Add x's free variables to the set
        """
        raise NotImplementedError

class Term(object):
    """Abstract base class of unifiable constructor applications."""

    def __init__(self):
        raise NotImplementedError, "'Term' is an abstract base class"

    def canonicalize(self):
        return self

    def occursCheck(self, v):
        # Return 'True' if any parameter mentions v
        for p in self.getParameters():
            if p.occursCheck(v): return True
        return False

    def getConstructor(self):
        raise NotImplemetnedError

    def getParameters(self):
        raise NotImplementedError

    def addFreeVariables(self, s):
        for p in self.getParameters(): p.addFreeVariables(s)

class Variable(object):
    """Abstract base class of unification variables."""

    def __init__(self):
        self._representative = None

    def canonicalize(self):
        canon = self
        # TODO
        # EntTy does not have _representative, thus raises an exception
        # Below try-except does not look good
        try:
            while canon._representative:
                canon = canon._representative
        except:
            pass
        finally:
            return canon

    def unifyWith(self, other):
        self._representative = other

    def occursCheck(self, v):
        return self is v

    def addFreeVariables(self, s):
        s.add(self)

class UnificationError(Exception):
    pass

def unify(x, y):
    """
    unify(x, y) -> z
    Unify two objects.  If the objects can be unified, the unified object
    is returned.
    If the objects cannot be unified, a UnificationError is raised.
    """
    # Canonicalize x and y
    x = x.canonicalize()
    y = y.canonicalize()

    # If equal, then succeed
    if x is y: return x

    # If occurs check fails, then fail
    if isinstance(y, Variable) and x.occursCheck(y):
        raise UnificationError, "occurs check failed"

    if isinstance(x, Variable) and y.occursCheck(x):
        raise UnificationError, "occurs check failed"

    # Attempt to unify terms
    if isinstance(x, Term):
        if isinstance(y, Term):
            # Terms are equal if they are the same constructor applied to
            # the same arguments
            if x.getConstructor() == y.getConstructor():
                x_params = x.getParameters()
                y_params = y.getParameters()

                # If this happens, the input is malformed
                if len(x_params) != len(y_params):
                    raise UnificationError, \
                          "wrong number of parameters to constructor"

                for x_p, y_p in zip(x_params, y_params):
                    unify(x_p, y_p)
            else:
                raise UnificationError, "type mismatch"

        else:                           # Variable
            y.unifyWith(x)

        # Return x, since it is canonical
        return x
    else:                               # Variable
        x.unifyWith(y)

        # Return y, since it is still canonical
        return y
