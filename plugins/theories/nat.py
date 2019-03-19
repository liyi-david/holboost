from kernel.macro import Macro, MacroFoldRule
from kernel.term import Sort, Construct, Const, Ind, Apply


class NatType(Macro):

    class FoldNatType(MacroFoldRule):
        @classmethod
        def fold(cls, term):
            if isinstance(term, Ind) and term.mutind_name == 'Coq.Init.Datatypes.nat' and term.ind_index == 0:
                return nat

            return None

    __instance = None

    def __new__(cls):
        if cls.__instance is None:
            cls.__instance = super(NatType, cls).__new__(cls)

        return cls.__instance

    @classmethod
    def name(cls):
        return "nat_type"

    def check(self, environment=None):
        return Sort.mkSet(), set()

    def render(self, environment=None, debug=False):
        return "nat"

    def unfold(self, environment=None):
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

    def check(self, environment=None):
        _, sideff_l = self.l.check(environment)
        _, sideff_r = self.r.check(environment)
        return Sort.mkProp(), set.union(sideff_l, sideff_r)

    def render(self, environment=None, debug=False):
        return "(%s %s %s)" % (
                self.l.render(environment, debug),
                self.opr,
                self.r.render(environment, debug),
                )

    def unfold(self):
        return Apply(
                self.oprmap[self.opr],
                self.l, self.r
                )


class NatValue(Macro):

    class FoldNatValue(MacroFoldRule):
        @classmethod
        def fold(cls, term):

            isnat = lambda t: isinstance(t, Construct) and t.mutind_name == 'Coq.Init.Datatypes.nat' and t.ind_index == 0
            is0 = lambda t: isnat(t) and t.constructor_index == 0

            if is0(term):
                return nat(0)
            elif isinstance(term, Apply) and isnat(term.func):
                v = 0
                while isinstance(term, Apply):
                    term, v = term.args[0], v + 1

                if is0(term):
                    return nat(v)
                elif isinstance(term, NatValue):
                    return nat(v + term.val)
                else:
                    return None
            else:
                return None



    @classmethod
    def name(cls):
        return "nat_value"

    def __init__(self, val):
        assert isinstance(val, int) and val >= 0, "non-natural number!"
        self.val = val

    def type(self, environment=None):
        return nat

    def check(self, environment=None):
        return nat, set()

    def render(self, environment=None, debug=False):
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
