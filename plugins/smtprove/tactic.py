from kernel.tactic import Tactic
from kernel.proofview import Proof

from .proofterm import SmtSolved

class SmtTactic(Tactic):

    @classmethod
    def run(cls, goal):

        # in what cases we can use smt?

        # how to convert env and goal to smt?

        # how to obtain the proofterm from smt?

        raise cls.TacticFailure
