from kernel.term import Term
from abc import ABCMeta, abstractmethod

class Tactic(metaclass=ABCMeta):

    class TacticFailure(Exception):
        pass

    name = "?"
    is_unreliable = False


    @classmethod
    @abstractmethod
    def run(cls, goal):
        """
        the result of running a tactic should be
        - an iterable of goals
        - raising a `TacticFailure` exception
        """
        pass

    __registered_tactics = []

    @classmethod
    def registered(cls):
        return cls.__registered_tactics

    @classmethod
    def register(cls):
        assert issubclass(cls, Tactic), "class %s is not a valid tactic, please check the inheritance" % str(tactic)

        Tactic.__registered_tactics.append(cls)
