from kernel.tactic import Tactic
from kernel.environment import ContextEnvironment
from kernel.term import Prod, Lambda, Binding
from kernel.proofview import Goal

class IntroTactic(Tactic):

    @classmethod
    def run(cls, g):
        if isinstance(g.formula(), Prod):
            new_goal = Goal(
                    g.formula().body,
                    ContextEnvironment(g.formula().get_binding(), g.env())
                    )
            g.give_proof(Lambda(g.formula().arg_name, g.formula().arg_type, new_goal))

            return [new_goal]
        else:
            raise cls.TacticFailure
