from kernel.interpretation import Interpretation
from kernel.term import *


class NatType(Interpretation):

    def render(self, environment, context=[], debug=False):
        return "N"

    def unfold(self):
        return Ind("Coq.Init.Datatypes.nat", 0)


class Nat(Interpretation):

    def __init__(self, val):
        assert isinstance(val, int) and val >= 0, "non-natural number!"
        self.val = val

    def render(self, environment, context=[], debug=False):
        return str(self.val)

    def unfold(self):
        if self.val == 0:
            return Construct("Coq.Init.Datatypes.nat", 0, 0)
        else:
            return Apply(
                    Construct("Coq.Init.Datatypes.nat", 0, 1), Nat(self.val - 1)
                    )

nat = NatType()
