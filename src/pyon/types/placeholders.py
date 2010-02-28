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
    def __init__(self, constraint, instance, inst_superclasses,
                 cls_superclasses, dict_type):
        assert isinstance(instance, pyon.types.classes.Instance)
        for sc in inst_superclasses:
            assert isinstance(sc, Derivation)
        for sc in cls_superclasses:
            assert isinstance(sc, Derivation)
        assert gluon.isExp(dict_type)

        self.constraint = constraint
        self.instance = instance
        self.instSuperclasses = inst_superclasses
        self.clsSuperclasses = cls_superclasses
        self.dictionaryType = dict_type

    def getDictionaryType(self):
        return self.dictionaryType

    def getCode(self, environment):
        gluon_types = pyon.types.gluon_types

        # The type for which this dictionary is derived
        this_instance_type = self.constraint.type

        # Get the code and type for each superclass.
        cls_superclass_vars = []    # Let-bound variables
        inst_superclass_vars = []    # Let-bound variables
        placeholders = []

        # Build the superclass dictionaries
        def make_superclass_dict(sc, var_list):
            cst = sc.constraint
            sc_ph, sc_code = sc.getCode(environment)
            sc_type = _classDictType(cst.typeClass, cst.type)
            var_list.append((sf.newVar(None), sc_type, sc_code))
            placeholders.extend(sc_ph)

        for sc in self.clsSuperclasses:
            make_superclass_dict(sc, cls_superclass_vars)

        for sc in self.instSuperclasses:
            make_superclass_dict(sc, inst_superclass_vars)

        # Determine type and dictionary parameters to use for constructing
        # instance methods
        typarams, constraints, head = self.instance.getScheme().instantiate()
        subst = unification.match(head, this_instance_type)

        def find_matching_constraint(c):
            # Find the superclass variable that matches this class constraint
            for (v, _, _), sc in \
                    zip(inst_superclass_vars, self.instSuperclasses) \
                    + zip(cls_superclass_vars, self.clsSuperclasses):
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
                m = sf.mkTyAppE(m, gluon_types.convertType(tp))
            if constraint_vars:
                m = sf.mkCallE(m, constraint_vars)
            methods.append(m)

        # Build the dictionary
        superclass_variable_exprs = [sf.mkVarE(v)
                                     for v, _, _ in cls_superclass_vars]
        expr = sf.mkDictE(self.instance.typeClass.getSystemFClass(),
                          gluon_types.convertType(this_instance_type),
                          superclass_variable_exprs,
                          methods)

        # Bind each superclass dictionary with let expressions
        for v, ty, c in reversed(cls_superclass_vars + inst_superclass_vars):
            pat = sf.mkVarP(v, ty)
            expr = sf.mkLetE(pat, c, expr)
        return (placeholders, expr)

def _classDictType(cls, type):
    """
    _classDictType(Class, FirstOrderType) -> Exp
    Create a System F class dictionary type.
    """
    return gluon.mkConAppE(gluon.noSourcePos, cls.getSystemFCon(),
                           [pyon.types.gluon_types.convertType(type)])
