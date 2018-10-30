from kernel.term import Term
from abc import ABCMeta, abstractmethod

class Tactic(metaclass=ABCMeta):

    class TacticFailure(Exception):
        pass

    name = "?"
    is_unreliable = False

    @classmethod
    def run(cls, goal, environment=None):
        """
        FINAL: I will fire myself if I ever override this function
        """
        result = cls._run(goal)
        assert isinstance(result, tuple) and len(result) == 2, "result of tactic should be in form of (proofterm, new goals)"
        proofterm, new_goals = result
        if cls.is_unreliable:
            if proofterm.type(environment) != goal.type(environment):
                raise TacticFailure("the unreliable tactic %s fails in post-tactic type checking" % cls.name)

        return proofterm, new_goals

    @classmethod
    @abstractmethod
    def _run(cls, goal):
        pass

    __registered_tactics = []

    @classmethod
    def register(cls):
        assert issubclass(cls, Tactic), "class %s is not a valid tactic, please check the inheritance" % str(tactic)

        Tactic.__registered_tactics.append(cls)
