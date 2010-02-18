"""
Placeholders used by type inference.  These are in a separate file to break
cyclic import dependences.
"""

import pyon.types.classes
import pyon.types.gluon_types
import pyon.unification as unification
import system_f as sf
import gluon

class RecVarPlaceholder(object):
    def __init__(self, variable, first_order_type):
        self._variable = variable
        self._type = first_order_type
        self._expression = sf.newExpPlaceholder()

    def __str__(self):
        return "RecVarPlaceholder(" + str(self._variable) + str(self._type) + ")"

    def getVariable(self):
        return self._variable

    def getFirstOrderType(self):
        return self._type

    def getExpression(self):
        return self._expression

    def setElaboration(self, elaboration):
        sf.setExpPlaceholder(self._expression, elaboration)

class DictPlaceholder(object):
    def __init__(self, constraint):
        self._constraint = constraint
        self._expression = sf.newExpPlaceholder()

    def __str__(self):
        return "DictPlaceholder(" + str(self._constraint) + ")"

    def getConstraint(self):
        return self._constraint

    def getExpression(self):
        return self._expression

    def setElaboration(self, elaboration):
        sf.setExpPlaceholder(self._expression, elaboration)

class Derivation(object):
    "A derivation of a class instance."

    def getCode(self, environment):
        """
        d.getCode([(ClassPredicate, sf.ObVariable)])
            -> ([sf.PlaceholderExpr], sf.Expression)

        Get code that performs this derivation.  If the derivation cannot
        be performed, raise an exception.
        """
        raise NotImplementedError, "'Derivation' is an abstract base class"

    def getDictionaryType(self):
        raise NotImplementedError, "'Derivation' is an abstract base class"

class IdDerivation(Derivation):
    "A derivation that uses an existing class instance."
    def __init__(self, constraint):
        self.constraint = constraint

    def getDictionaryType(self):
        return self.constraint.getDictionaryType()

    def getCode(self, environment):
        constraint = self.constraint
        for dc, v in environment:
            if constraint == dc:
                return ([], sf.mkVarE(v))

        # else, needed class is not in the environment
        placeholder = pyon.type_inference.DictPlaceholder(self.constraint)
        return ([placeholder], placeholder.getExpression())

class InstanceDerivation(Derivation):
    "A derivation that uses a class instance definition."
    def __init__(self, constraint, instance, superclasses, dict_type):
        assert isinstance(instance, pyon.types.classes.Instance)
        for sc in superclasses:
            assert isinstance(sc, Derivation)
        assert gluon.isExp(dict_type)

        self.constraint = constraint
        self.instance = instance
        self.superclasses = superclasses
        self.dictionaryType = dict_type

    def getDictionaryType(self):
        return self.dictionaryType

    def getCode(self, environment):
        # Get the code and type for each superclass.
        superclass_vars = []    # Let-bound variables
        superclass_code = []
        placeholders = []

        # Build the superclass dictionaries
        for sc in self.superclasses:
            sc_ph, sc_code = sc.getCode(environment)
            sc_type = sc.getDictionaryType()
            superclass_vars.append((sf.newVar(None), sc_type))
            superclass_code.append(sc_code)
            placeholders += sc_ph

        # Determine type and dictionary parameters to use for constructing
        # instance methods
        typarams, constraints, head = self.instance.getScheme().instantiate()
        subst = unification.match(head, self.constraint.type)

        def find_matching_constraint(c):
            # Find the superclass variable that matches this class constraint
            for (v, _), sc in zip(superclass_vars, self.superclasses):
                if sc.constraint == c: return sf.mkVarE(v)

            # Else, a matching constraint was not found
            raise RuntimeError, "Could not create instance derivation"

        typarams = [p.rename(subst) for p in typarams]
        constraint_vars = [find_matching_constraint(c.rename(subst))
                           for c in constraints]

        # Create instance methods.  Apply each method to the instance's type
        # parameters and dictionary parameters.
        methods = []
        for m in self.instance.methods:
            for tp in typarams:
                m = sf.mkTyAppE(m, pyon.types.gluon_types.convertType(tp))
            if constraint_vars:
                m = sf.mkCallE(m, constraint_vars)
            methods.append(m)

        # Build the dictionary
        superclass_variable_exprs = [sf.mkVarE(v) for v, _ in superclass_vars]
        expr = sf.mkDictE(self.instance.typeClass.getSystemFClass(),
                          self.dictionaryType,
                          superclass_variable_exprs,
                          methods)

        # Bind each superclass dictionary with let expressions
        for (v, ty), c in reversed(zip(superclass_vars,
                                       superclass_code)):
            pat = sf.mkVarP(v, ty)
            expr = sf.mkLetE(pat, c, expr)
        return (placeholders, expr)

