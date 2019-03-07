from kernel.tactic import Tactic
from kernel.environment import ContextEnvironment
from kernel.term import Lambda, Apply, Ind, Sort, Const, Prod, Binding, Rel
from kernel.proofview import Goal, Proof


class ApplyTactic(Tactic):

    @classmethod
    def run(cls, g):
        gf = g.formula()
        env = g.env()
