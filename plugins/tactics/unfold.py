from kernel.tactic import Tactic
from kernel.environment import ContextEnvironment
from kernel.term import Prod, Lambda, Binding, Apply, Const
from kernel.proofview import Goal

class UnfoldTactic(Tactic):

    @classmethod
    def run(cls, g):
        gf = g.formula()
        if isinstance(gf, Apply) and isinstance(gf.func, Const):
            new_goal = Goal(
                    Apply(
                        g.env().constant(gf.func.name)[0].body,
                        *gf.args
                        ),
                    g.env()
                    )
            g.give_proof(new_goal)
            print(new_goal)

            return [new_goal]
        else:
            raise cls.TacticFailure
