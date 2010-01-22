
import unicodedata

from pyon.types.hmtype import *
import pyon.types.classes

_FORALL = unicodedata.lookup('FOR ALL')

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
        for c in constraints:
            assert isinstance(c, pyon.types.classes.ClassPredicate)
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
        # Show as forall a b c. constraints => type
        visible_vars = visible_vars + self.qvars
        var_list = [v.showWorker(PyonTypeBase.PREC_OUTER, visible_vars)
                    for v in self.qvars]
        var_doc = pretty.space(pretty.punctuate(',', var_list))
        quantifier = pretty.abut(pretty.space(_FORALL, var_doc), '.')

        constraints = self.constraints
        if len(constraints) == 0:
            constraint_doc = None
        elif len(constraints) == 1:
            constraint_doc = constraints[0].showWorker(PyonTypeBase.PREC_OUTER,
                                                       visible_vars)
            constraint_doc = pretty.space(constraint_doc, '=>')
        else:
            constraint_docs = [c.showWorker(PyonTypeBase.PREC_OUTER,
                                            visible_vars)
                               for c in constraints]
            constraint_doc = pretty.parens(pretty.space(pretty.punctuate(',', constraint_docs)))
            constraint_doc = pretty.space(constraint_doc, '=>')

        fotype = self.type.showWorker(PyonTypeBase.PREC_FUN - 1,
                                      visible_vars)
        return pretty.linewr(pretty.space(quantifier, constraint_doc),
                             fotype, 2)

    def instantiate(self):
        """
        scheme.instantiate() -> (constraints, type)
        Instantiate a type scheme by creating fresh variables for each type.
        """
        # Rename each type variable to a fresh variable
        mapping = dict((v, TyVar()) for v in self.qvars)
        t = self.type.rename(mapping)
        cs = [c.rename(mapping) for c in self.constraints]
        return (cs, t)

    def addFreeVariables(self, s):
        # The type scheme's quantified variables must not be free
        assert not len(set.intersection(set(self.qvars), s))

        for c in self.constraints: c.addFreeVariables(s)
        self.type.addFreeVariables(s)

        for v in self.qvars: s.discard(v)

