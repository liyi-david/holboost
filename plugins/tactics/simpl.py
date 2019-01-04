from kernel.tactic import Tactic
from kernel.environment import ContextEnvironment
from kernel.term import Lambda, Apply
from kernel.proofview import Goal, Proof

class SimplTactic(Tactic):

    @classmethod
    def run(cls, g):
        gf = g.formula()
        if isinstance(gf, Apply) and isinstance(gf.func, Lambda):
            new_formula = gf.func.body.rels_subst([gf.args[0]])
            if len(gf.args) > 1:
                new_formula = Apply(new_formula, *gf.args[1:])

            new_goal = Goal(new_formula, g.env())
            return Proof(new_goal, new_goal)
        else:
            raise cls.TacticFailure
