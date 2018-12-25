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

    coq_Z = 'Coq.Numbers.BinNums.Z'
    coq_positive = 'Coq.Numbers.BinNums.positive'

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
            return Construct(self.coq_Z, 0, 0)
        else:
            constructor = Construct(self.coq_Z,  0, 1 if self.value > 0 else 2)
            v = abs(self.value)
            bs = bin(v)[3:]

            # since self.value != 0, at least the highest bit is 1
            result = Construct(self.coq_positive, 0, 2)
            for bit in bs:
                result = Apply(
                        Construct(self.coq_positive, 0, 0 if bit == "1" else 1),
                        result
                        )

            result = Apply(constructor, result)
            return result

    @classmethod
    def fold(cls, t):
        if isinstance(t, Apply) and isinstance(t.func, Construct) and t.func.mutind_name == cls.coq_Z:
            if t.func.constructor_index == 0:
                return integer(0)
            else:
                sgn = 1 if t.func.constructor_index == 1 else -1

            pos = t.args[0]
            bits = ''
            while isinstance(pos, (Apply, Construct)):
                if isinstance(pos, Construct) and pos.mutind_name == cls.coq_positive and pos.constructor_index == 2:
                    bits = '1' + bits
                    break
                elif isinstance(pos, Apply) and isinstance(pos.func, Construct) and pos.func.mutind_name == cls.coq_positive:
                    bits = ('1' if pos.func.constructor_index == 0 else '0') + bits
                    pos = pos.args[0]
                else:
                    raise Macro.MacroFoldFailure()

            return integer(sgn * int(bits, 2))



integer = BinaryNumberType()
BinaryNumberValue.register()
