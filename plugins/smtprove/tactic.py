from kernel.tactic import Tactic
from .proofterm import SmtProof

class SmtTactic(Tactic):

    @classmethod
    def _run(cls, goal, environment=None):
        return SmtProof(goal), []
