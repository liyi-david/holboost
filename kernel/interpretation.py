"""
interpretations are used to handle the cases where we do not want to use low level concepts in Coq, Isabella, etc. for example,
natural numbers in Coq are represented by unary terms, e.g. 3 = (S (S (S O))). This may simplifies mathematical reasoning in Coq,
but it of course makes it harder to reason program properties. Instead, we want to use a natural number term as its interpretation.

"""
from .term import Term

import abc

class Interpretation(Term, metaclass=abc.ABCMeta):

    def __init__(self):
        pass

    @abc.abstractmethod
    def type(self, environment, context=[]) -> 'Term':
        pass

    @abc.abstractmethod
    def render(self, environment=None, context=[], debug=False) -> 'str':
        pass

    @abc.abstractmethod
    def unfold(self):
        pass


class Proved(Interpretation):
    def __init__(self, prop: 'Term', proof: 'Term'):
        Interpretation.__init__(self)

        self.prop = prop
        self.proof = proof

    def type(self, environment, context=[]) -> 'Term':
        return self.prop.type(environment, context)

    def render(self, environment=None, context=[], debug=False) -> 'str':
        proofstr = ""
        if debug:
            proofstr = " BY %s" % self.proof.render(environment, context, debug)

        return "%s [PROVED%s]" % (
                self.prop.render(environment, context, debug),
                proofstr
                )

    def unfold(self):
        raise Exception('Unimplemented')

    def __eq__(self, t):
        raise Exception('Unimplemented')

    def subterms(self):
        raise Exception('Unimplemented')

    def subterms_subst(self):
        raise Exception('Unimplemented')
