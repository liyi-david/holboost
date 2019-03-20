from kernel.macro import Macro, MacroFoldRule
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

    def type(self, environment=None):
        return Sort.mkSet()

    def render(self, environment=None, debug=False):
        return "int"

    def unfold(self):
        return Ind('Coq.Numbers.BinNums.Z', 0)

    # ======================== operations on binary numbers ===================

    def _le(self, l, r):
        return BinaryNumberExpr('<=', l, r)

    def _lt(self, l, r):
        return BinaryNumberExpr('<', l, r)

    def _eq(self, l, r):
        return BinaryNumberExpr('=', l, r)


class BinaryNumberExpr(Macro):

    oprmap = {
            '+'  : None,
            '-'  : None,
            '*'  : None,
            '/'  : None,
            '>'  : None,
            '>='  : None,
            '<=' : Const('Coq.ZArith.BinInt.Z.le'),
            '<'  : Const('Coq.ZArith.BinInt.Z.lt'),
            '='  : Apply(Ind('Coq.Init.Logic.eq', 0), BinaryNumberType()),
            '=='  : None,
            '!='  : None,
            }

    def __init__(self, opr, l, r=None):
        assert opr in self.oprmap, "unsupported operator %s" % opr
        self.opr = opr
        self.l = l
        self.r = r

    def type(self, environment=None):
        return Sort.mkProp()

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

class BinaryNumberValue(Macro):

    coq_Z = 'Coq.Numbers.BinNums.Z'
    coq_positive = 'Coq.Numbers.BinNums.positive'

    class FoldBinaryNumberValue(MacroFoldRule):

        @classmethod
        def fold(cls, t):
            if isinstance(t, Apply) and isinstance(t.func, Construct) and t.func.mutind_name == BinaryNumberValue.coq_Z:
                if t.func.constructor_index == 0:
                    return integer(0)
                else:
                    sgn = 1 if t.func.constructor_index == 1 else -1

                pos = t.args[0]
                bits = ''
                while isinstance(pos, (Apply, Construct)):
                    if isinstance(pos, Construct) and pos.mutind_name == BinaryNumberValue.coq_positive and pos.constructor_index == 2:
                        bits = '1' + bits
                        break
                    elif isinstance(pos, Apply) and isinstance(pos.func, Construct) and pos.func.mutind_name == BinaryNumberValue.coq_positive:
                        bits = ('1' if pos.func.constructor_index == 0 else '0') + bits
                        pos = pos.args[0]
                    else:
                        raise cls.MacroFoldFailure()

                return integer(sgn * int(bits, 2))




    def __init__(self, value):
        self.value = value

    @classmethod
    def name(cls):
        return "binary_number_value"

    def type(self, environment=None):
        return integer

    def check(self, environment=None):
        return integer, set()

    def render(self, environment=None, debug=False):
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

integer = BinaryNumberType()
