from kernel.macro import Macro
from kernel.term import Sort, Ind, Construct, Apply, Const


class BinaryNumberType(Macro):

    __instance = None

    def __new__(cls):
        if cls.__instance is None:
            cls.__instance = super(BinaryNumberType, cls).__new__(cls)

        return cls.__instance

    def __init__(self):
        pass

    def __call__(self, value):
        assert isinstance(value, int), "a binary number must be initialized by an integer!"
        return BinaryNumberValue(value)

    @classmethod
    def name(cls):
        return "binary_number_type"

    def type(self, environment=None, context=[]):
        return Sort.mkSet()

    def render(self, environment=None, context=[], debug=False):
        return "int"

    def unfold(self):
        return Ind('Coq.Numbers.BinNums.Z', 0)

    # ======================== operations on binary numbers ===================

    def _le(self, l, r):
        return BinaryNumberComparison('<=', l, r)

    def _lt(self, l, r):
        return BinaryNumberComparison('<', l, r)

    def _eq(self, l, r):
        return BinaryNumberComparison('=', l, r)


class BinaryNumberComparison(Macro):

    oprmap = {
            '<=' : Const('Coq.ZArith.BinInt.Z.le'),
            '<'  : Const('Coq.ZArith.BinInt.Z.lt'),
            '='  : Apply(Ind('Coq.Init.Logic.eq', 0), BinaryNumberType())
            }

    @classmethod
    def name(cls):
        return "binary_number_comparison"

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


class BinaryNumberValue(Macro):

    def __init__(self, value):
        self.value = value

    @classmethod
    def name(cls):
        return "binary_number_value"

    def type(self, environment=None, context=[]):
        return integer

    def check(self, environment=None, context=[]):
        return integer, set()

    def render(self, environment=None, context=[], debug=False):
        return str(self.value)

    def unfold(self):
        if self.value == 0:
            return Construct('Coq.Numbers.BinNums.Z', 0, 0)
        else:
            constructor = Construct('Coq.Numbers.BinNums.Z', 0, 1 if self.value > 0 else 2)
            v = abs(self.value)
            bs = bin(v)[3:]

            # since self.value != 0, at least the highest bit is 1
            result = Construct('Coq.Numbers.BinNums.positive', 0, 2)
            for bit in bs:
                result = Apply(
                        Construct('Coq.Numbers.BinNums.positive', 0, 0 if bit == "1" else 1),
                        result
                        )

            result = Apply(constructor, result)
            return result


integer = BinaryNumberType()
