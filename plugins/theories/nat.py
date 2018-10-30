from kernel.macro import Macro
from kernel.term import *


class NatType(Macro):

    @classmethod
    def name(cls):
        return "nat_type"

    def type(self, environment=None, context=[]):
        return Sort.mkSet()

    def check(self, environment=None, context=[]):
        return Sort.mkSet(), set()

    def render(self, environment=None, context=[], debug=False):
        return "nat"

    def unfold(self):
        return Ind("Coq.Init.Datatypes.nat", 0)

    def __call__(self, val):
        """
        invoke NatValue and construct natural numbers, e.g. nat(0)
        """
        return NatValue(val)


class NatValue(Macro):

    @classmethod
    def name(cls):
        return "nat_value"

    def __init__(self, val):
        assert isinstance(val, int) and val >= 0, "non-natural number!"
        self.val = val

    def type(self, environment=None, context=[]):
        return nat

    def check(self, environment=None, context=[]):
        return nat, set()

    def render(self, environment=None, context=[], debug=False):
        return str(self.val)

    def unfold(self):
        if self.val == 0:
            return Construct("Coq.Init.Datatypes.nat", 0, 0)
        else:
            return Apply(
                    Construct("Coq.Init.Datatypes.nat", 0, 1), NatValue(self.val - 1)
                    )


nat = NatType()
