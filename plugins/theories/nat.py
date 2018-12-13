from kernel.macro import Macro
from kernel.term import Sort, Construct, Const, Ind, Apply


class NatType(Macro):

    __instance = None

    def __new__(cls):
        if cls.__instance is None:
            cls.__instance = super(NatType, cls).__new__(cls)

        return cls.__instance

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

    # ============================ operations on natural numbers ==============
    # ......

    def _le(self, l, r):
        return NatComparison('<=', l, r)

    def _lt(self, l, r):
        return NatComparison('<', l, r)

    def _eq(self, l, r):
        return NatComparison('=', l, r)


class NatComparison(Macro):

    oprmap = {
            '<=' : Ind('Coq.Init.Peano.le', 0),
            '<'  : Const('Coq.Init.Peano.lt'),
            '='  : Apply(Ind('Coq.Init.Logic.eq', 0), NatType())
            }

    @classmethod
    def name(cls):
        return "net_comparison"

    def __init__(self, opr, l, r):
        assert opr in ('<=', '<', '='), "unsupported comparison operator %s" % opr
        self.opr = opr
        self.l = l
        self.r = r

    def type(self, environment=None, context=[]):
        return Sort.mkProp()

    def check(self, environment=None, context=[]):
        _, sideff_l = self.l.check(environment, context)
        _, sideff_r = self.r.check(environment, context)
        return Sort.mkProp(), set.union(sideff_l, sideff_r)

    def render(self, environment=None, context=[], debug=False):
        return "(%s %s %s)" % (
                self.l.render(environment, context, debug),
                self.opr,
                self.r.render(environment, context, debug),
                )

    def unfold(self):
        return Apply(
                self.oprmap[self.opr],
                self.l, self.r
                )


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

    def to_json(self):
        json = Macro.to_json(self)
        json.update({ "value": self.val })
        return json


nat = NatType()
