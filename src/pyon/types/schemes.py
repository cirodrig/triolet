
from pyon.types.hmtype import *
import pyon.types.classes

###############################################################################
# Type schemes

def instantiateVariables(vars):
    """
    instantiateVariables(variable-list) -> mapping

    Instantiate some type variables.  Each variable is mapped to a fresh type
    variable, and the mapping is returned.
    """
    return dict((v, TyVar()) for v in vars)

class TyScheme(PyonTypeBase):
    """
    A type scheme: forall (qvars). (constraints) => (t)
    """

    def __init__(self, qvars, constraints, t):
        assert isinstance(constraints, pyon.types.classes.Constraints)
        self.qvars = qvars
        self.constraints = constraints
        self.type = t

    @classmethod
    def forall(cls, num_vars, body, constraints = lambda *xs: pyon.types.classes.noConstraints):
        """
        TyScheme.forall(int, make-body) -> new type scheme
        TyScheme.forall(int, make-body, make-constraints) -> new type scheme

        Create a new type scheme quantified over new variables.
        """
        vars = tuple(TyVar() for v in range(num_vars))
        t = apply(body, vars)
        csts = apply(constraints, vars)
        return cls(vars, csts, t)

    def rename(self, mapping):
        # Bound variables should never be renamed and variables should not be
        # shadowed
        for v in self.qvars:
            if v in mapping.keys():
                raise ValueError, "Attempt to rename variable bound by type scheme"

        # Rename variables in this type scheme
        return TyScheme(self.qvars,
                        self.constraints.rename(mapping),
                        self.type.rename(mapping))

    def showWorker(self, precedence, visible_vars):
        # Show as forall a b c. 
        var_list = [v.showWorker(PyonTypeBase.PREC_OUTER, visible_vars) \
            for v in self.qvars]
        var_doc = pretty.space(pretty.punctuate(',', var_list))
        quantifier = pretty.space("forall", pretty.abut(var_doc, '.'))
        monotype = self.type.showWorker(PyonTypeBase.PREC_FUN - 1,
                                        visible_vars + qvars)
        return pretty.linewr(quantifier, monotype, 2)

    def instantiate(self):
        """
        scheme.instantiate() -> type
        Instantiate a type scheme by creating fresh variables for each type.
        """
        # Rename each type variable to a fresh variable
        mapping = dict((v, TyVar()) for v in self.qvars)
        return self.type.rename(mapping)

    def addFreeVariables(self, s):
        # The type scheme's quantified variables must not be free
        assert not len(set.intersection(set(self.qvars), s))

        self.constraints.addFreeVariables(s)
        self.type.addFreeVariables(s)

        for v in self.qvars: s.discard(v)

def generalize(t, constraints):
    """
    generalize(t, constraints) -> (scheme, constraints)

    Generalize a type by quantifying over all free type variables.
    """
    (dependent_constraints, free_constraints) = \
        constraints.generalizeOver(t.freeVariables())

    scheme = TyScheme(list(t.freeVariables()), dependent_constraints, t)
    return (scheme, free_constraints)

