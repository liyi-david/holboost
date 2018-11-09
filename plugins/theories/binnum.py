from kernel.macro import Macro
from kernel.term import Sort, Ind, Construct, Apply


class BinaryNumberType(Macro):

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

    def render(self, environment=None, context=[]):
        return "int"

    def unfold(self):
        return Ind('Coq.Numbers.BinNums.Z', 0)


class BinaryNumberValue(Macro):

    def __init__(self, value):
        self.value = value

    @classmethod
    def name(cls):
        return "binary_number_value"

    def type(self, environment=None, context=[]):
        return integer

    def render(self, environment=None, context=[]):
        return str(self.value)

    def unfold(self):
        if self.value == 0:
            return Construct('Coq.Numbers.BinNums.Z', 0, 0)
        else:
            constructor = Construct('Coq.Numbers.BinNums.Z', 0, 1 if self.value > 0 else 0)
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
