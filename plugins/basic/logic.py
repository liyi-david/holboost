from kernel.macro import Macro
from kernel.term import Apply, Ind, Const
from enum import Enum


class LogicOpr(Macro):

    class OprType(Enum):
        land = 1
        lor = 2
        lnot = 3

    def __init__(self, opr, l, r=None):
        self.opr = opr
        self.l = l
        self.r = r

    def __repr__(self):
        return self.render()

    def name(self):
        return "logic_operation"

    def render(self, environment=None, context=[], debug=False):
        if self.opr is self.OprType.lnot:
            return "(~ %s)" % (self.l.render(environment, context, debug))
        elif self.opr is self.OprType.land:
            return "(%s ∧ %s)" % (
                    self.l.render(environment, context, debug),
                    self.r.render(environment, context, debug)
                    )
        elif self.opr is self.OprType.lor:
            return "(%s ∨ %s)" % (
                    self.l.render(environment, context, debug),
                    self.r.render(environment, context, debug)
                    )
        else:
            raise Macro.MacroAbuse("invalid logic operator %s" % (str(self.opr)))

    def unfold(self):
        if self.opr is self.OprType.lnot:
            return Apply(
                    Const('Coq.Init.Logic.not'),
                    self.l
                    )
        elif self.opr is self.OprType.land:
            return Apply(
                    Ind('Coq.Init.Logic.and', 0),
                    self.l, self.r
                    )
        elif self.opr is self.OprType.lor:
            return Apply(
                    Ind('Coq.Init.Logic.or', 0),
                    self.l, self.r
                    )
        else:
            raise Macro.MacroAbuse("invalid logic operator %s" % (str(self.opr)))


def land(l, r):
    return LogicOpr(LogicOpr.OprType.land, l, r)

def lor(l, r):
    return LogicOpr(LogicOpr.OprType.lor, l, r)

def lnot(l):
    return LogicOpr(LogicOpr.OprType.lnot, l)
