"""
First-order unification.
"""

import pyon.pretty as pretty

class Unifiable(object):
    """Abstract base class of objects that can be unified."""

    def __init__(self):
        raise NotImplementedError, "'Unifiable' is an abstract base class"

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

    def rename(self, substitution):
        """
        x.rename(substitution) -> object

        Apply a substitution to x, possibly creating a new object.  The
        original object remains unchanged.  The substituted value is
        returned.
        """
        raise NotImplementedError

class Term(Unifiable):
    """Abstract base class of unifiable constructor applications."""

    def __init__(self):
        raise NotImplementedError, "'Term' is an abstract base class"

    def __eq__(self, other):
        raise NotImplementedError

    def occursCheck(self, v):
        # Return 'True' if any parameter mentions v
        for p in self.getParameters():
            if p.occursCheck(v): return True
        return False

    def getConstructor(self):
        raise NotImplementedError

    def getParameters(self):
        raise NotImplementedError

    def addFreeVariables(self, s):
        for p in self.getParameters(): p.addFreeVariables(s)

class Variable(Unifiable):
    """Abstract base class of unification variables."""

    def __init__(self):
        self._representative = None

    def canonicalize(self):
        canon = self

        # Find representative of this variable
        while canon._representative:
            canon = canon._representative

            # If representative is not a variable, it is canonical
            # canonicalize method
            if not isinstance(canon, Variable): return canon

        return canon

    def unifyWith(self, other):
        self._representative = other

    def occursCheck(self, v):
        return self is v

    def addFreeVariables(self, s):
        if self._representative: self.canonicalize().addFreeVariables(s)
        else: s.add(self)

    def rename(self, s):
        if self._representative: return self.canonicalize().rename(s)
        else:
            # Look up this variable's value in the substitution;
            # default to self.  Then canonicalize.
            # Don't apply the substitution to the result.
            return canonicalize(s.get(self, self))

def canonicalize(x):
    if isinstance(x, Variable): return x.canonicalize()
    else: return x

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
    x = canonicalize(x)
    y = canonicalize(y)

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

                return x
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

def match(x, y):
    """
    match(x, y) -> substitution or None

    Match x against y.  If there is a substitution that unifies x with y, the
    substitution is returned.  The inputs are not modified.

    Substitutions may be rendered invalid if unify() is called.
    """
    substitution = {}

    def semi_unify(x, y):
        "Semi-unification: extend the substitution as needed to make x match y"
        # Canonicalize x and y
        x = canonicalize(x)
        y = canonicalize(y)

        # If x is a term, match its head against y
        if isinstance(x, Term): match_head(x, y, semi_unify)

        else:
            # X is a variable; try substituting it
            # Is x in the mapping already?
            x_value = substitution.get(x)

            # If substitution succeeded, match x against y without further
            # substitution
            if x_value is not None: match_head(x_value, y, compare)

            # Otherwise, add the mapping x |-> y and succeed
            else: substitution[x] = y

    def compare(x, y):
        "Comparison: decide whether x is equal to y (don't substitute)"
        # Canonicalize x and y
        x = canonicalize(x)
        y = canonicalize(y)

        match_head(x, y, compare)

    def match_head(x, y, compare_subterm):
        # x and y have been canonicalized
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
                        compare_subterm(x_p, y_p)
                else: raise UnificationError
            else: raise UnificationError
        else:
            # X is a variable; y must be identical
            if x is not y: raise UnificationError
            # Otherwise, succeed

    # Body of function
    try:
        semi_unify(x, y)
        return substitution
    except UnificationError, e: return None
