"""
interpretations are used to handle the cases where we do not want to use low level concepts in Coq, Isabella, etc. for example,
natural numbers in Coq are represented by unary terms, e.g. 3 = (S (S (S O))). This may simplifies mathematical reasoning in Coq,
but it of course makes it harder to reason program properties. Instead, we want to use a natural number term as its interpretation.

"""
from .term import Term

import abc

class Macro(Term, metaclass=abc.ABCMeta):

    class MacroAbuse(Exception):
        pass

    @classmethod
    def macro_name(cls):
        assert type(cls) is not Macro, "cannot evaluate the name of Macro itself"
        return str(cls).split("'")[1]

    def type(self, environment=None) -> 'Term':
        return self.unfold(environment).type(environment)

    def check(self, environment=None):
        return self.unfold(environment).check(environment)

    def __eq__(self, t):
        if self is t:
            return True
        else:
            return self.unfold() == t

    def subterms(self):
        raise Macro.MacroAbuse

    def subterms_subst(self, subterms):
        raise Macro.MacroAbuse

    @abc.abstractmethod
    def unfold(self, environment=None) -> 'Term':
        pass

    def to_json(self):
        return {
                "node": "macro",
                "macro_name": self.macro_name(),
                "macro_repr": repr(self)
                }

    """
    interpretation registeration mechanism

    this allows plugins to register their interpretations
    """
    class MacroFoldFailure(Exception):
        """
        any foldable Macro should raise this exception when the folding process fails
        """
        pass

    __registered_macros = {}

    @classmethod
    def register(cls):
        if cls.macro_name() not in cls.__registered_macros:
            cls.__registered_macros[cls.macro_name()] = cls
        else:
            raise Exception("interpretation %s already exist!" % cls.name())

    @classmethod
    def fold(cls, term):
        """
        fold a term as macro.
        """
        if cls is not Macro:
            raise cls.MacroFoldFailure("the macro %s does not support fold feature!" % cls.macro_name())

        # fold from the root
        for _, macro in cls.__registered_macros.items():
            try:
                folden = macro.fold(term)
                if folden is not None:
                    return folden
            except cls.MacroFoldFailure as err:
                pass

        # fold the subterms
        try:
            folden_subterms = []
            for t in term.subterms():
                folden_subterms.append(t.autofold())
                if folden_subterms[-1] is None:
                    return term

            return term.subterms_subst(folden_subterms)
        except cls.MacroFoldFailure:
            pass

        return term



    # ============================ operators ==================================

    # only type macros need to implement the following operators.

    def _eq(self, l, r):
        raise self.MacroAbuse("'=' is not implemented in the macro %s" % str(type(self)))

    def _neq(self, l, r):
        raise self.MacroAbuse("'!=' is not implemented in the macro %s" % str(type(self)))

    def _le(self, l, r):
        raise self.MacroAbuse("'<=' is not implemented in the macro %s" % str(type(self)))

    def _lt(self, l, r):
        raise self.MacroAbuse("'<' is not implemented in the macro %s" % str(type(self)))

    def _ge(self, l, r):
        return self._le(r, l)

    def _gt(self, l, r):
        return self._lt(r, l)


class Proof(Term, metaclass=abc.ABCMeta):

    """
    A term is called provable, if and only if it is proved by some plugins in holboost. Since the tool
    is not as strict as Coq, precise proof term is not always required. Instead, a plugin may inherit the
    class `Provable` and invoke any proof checker they like.

    Holboost will try to reproduce the proof through running the proof obligations generated by get_proof_obligation
    """

    class ProofTermAbuse(Exception):
        pass

    class ProofObligation:
        pass

    def __init__(self):
        self.proved_formula = None

    @abc.abstractmethod
    def get_proof_obligation(self) -> 'Provable.ProofObligation':
        pass

    def type(self, environment=None, context=[]):
        return self.proved_formula

    def check(self, environment=None, context=[]):
        raise Provable.ProvableTermAbuse

    def __eq__(self, t):
        raise Provable.ProvableTermAbuse

    def subterms(self):
        raise Provable.ProvableTermAbuse

    def subterms_subst(self):
        raise Provable.ProvableTermAbuse
