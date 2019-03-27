from kernel.macro import Macro, MacroFoldRule
from kernel.term import Sort, Construct, Const, Ind, Apply

class UnitType(Macro):

    class FoldUnitType(MacroFoldRule):
        @classmethod
        def fold(cls, term):
            if isinstance(term, Ind) and term.mutind_name == 'Coq.Init.Datatypes.unit' and term.ind_index == 0:
                return UnitType()

            return None

    __instance = None

    def __new__(cls):
        if cls.__instance is None:
            cls.__instance = super(UnitType, cls).__new__(cls)

        return cls.__instance

    def __call__(self):
        return UnitValue()

    def check(self, environment=None):
        return Sort.mkSet(), set()

    def render(self, environment=None, debug=False):
        return "unit"

    def unfold(self, environment=None):
        return Ind("Coq.Init.Datatypes.unit", 0)


class UnitValue(Macro):

    class FoldUnitValue(MacroFoldRule):
        @classmethod
        def fold(cls, term):
            if isinstance(term, Construct) and term.mutind_name == 'Coq.Init.Datatypes.unit':
                return UnitValue()

    __instance = None

    def __new__(cls):
        if cls.__instance is None:
            cls.__instance = super(UnitValue, cls).__new__(cls)

        return cls.__instance

    def type(self, environment=None):
        return UnitType()

    def check(self, environment=None):
        return UnitType(), set()

    def render(self, environment=None, debug=False):
        return "()"

    def unfold(self):
        return Construct("Coq.Init.Datatypes.unit", 0, 0)

    def to_json(self):
        json = Macro.to_json(self)
        json.update({ "value": self.val })
        return json


unit = UnitType()
