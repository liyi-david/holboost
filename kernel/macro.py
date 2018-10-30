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
    @abc.abstractmethod
    def name(cls):
        """
        return the name of the interpretation
        """
        pass

    def type(self, environment, context=[]) -> 'Term':
        return self.unfold().type(environment, context)

    def check(self, environment, context=[]):
        return self.unfold().check(environment, context)

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
    def unfold(self) -> 'Term':
        pass

    @classmethod
    def fold(cls, term):
        """
        fold a term as macro, will be invoked automatically when the condition returned by
        auto_fold_on is satisfied.

        neither or both the two functions should be overwritten.
        """
        raise cls.MacroAbuse("unimplemented fold function")

    @classmethod
    def auto_fold_on(cls):
        """
        returns:
            - a lambda boolean function to check whether a term is going to be fold automatically
            - None indicating this macro does not support auto-folding feature
        """
        return None


    """
    interpretation registeration mechanism

    this allows plugins to register their interpretations
    """

    __registered_macros = {}
    __autofold_filters = {}

    @classmethod
    def register(cls):
        if cls.name() not in cls.__registered_macros:
            cls.__registered_macros[cls.name()] = cls
            if cls.auto_fold_on() is not None:
                cls.__autofold_filters[cls] = cls.auto_fold_on()
        else:
            raise Exception("interpretation %s already exist!" % cls.name())


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
