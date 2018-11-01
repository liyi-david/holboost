from .environment import Environment
from .term import Term, Sort


class Proofview:

    """
    A proofview is used to describe and store the progress of proving a certain formula.
    It follows the concept of proofview in Coq but does not precisely follow its definition.
    """

    class Goal:
        def __init__(self, goal_formula, proofview):
            self.__formula = goal_formula
            self.__proof = None
            self.__proofview = proofview

        def formula(self):
            return self.__formula

        def give_proof(self, proof):
            if proof.type(self.__proofview.env()) != self.__formula:
                raise TypeError("type mismatch between the goal and the given proof")

            self.__proof = proof

            # the goal is closed
            self.__proofview.close_goal(self)

        def closed(self):
            return self.__proof is not None

        def __repr__(self):
            return "<%s Goal: %s>" % ("Closed" if self.closed() else "Pending", self.__formula)

    def __init__(self, goal_formula, env=None):
        if not isinstance(goal_formula, Term):
            raise TypeError("type of the goal must be a Holboost term.")

        if goal_formula.type(env) != Sort.mkProp():
            raise TypeError("only propositions can be proved.")

        self.__goal = goal_formula
        self.__proof = None
        self.__pending_goals = []
        self.__closed_goals = []
        self.__env = env if env is not None else Environment.default()

        self.__pending_goals.append(self.Goal(goal_formula, self))

        if self.__env is None:
            raise Exception("cannot prove anything with no environment (nor default environment) provided!")

    def goals(self):
        return tuple(self.__pending_goals)

    def close_goal(self, goal):
        assert goal in self.__pending_goals, "somehow the goal is not in the pending list"
        assert goal.closed(), "cannot close a goal with no proof"

        self.__pending_goals.remove(goal)
        self.__closed_goals.append(goal)

    def closed(self):
        return len(self.__pending_goals) == 0

    def env(self): return self.__env

    def __repr__(self):
        if self.closed():
            return "<proofview on %s, closed>" % (
                    self.__goal.render(self.__env)
                    )
        else:
            return "<proofview on %s, %d goals pending>" % (
                    self.__goal.render(self.__env),
                    len(self.__pending_goals)
                    )

    def __str__(self):
        if self.closed():
            return repr(self)
        else:
            return repr(self) + "\n\n" + "\n".join(map(
                    lambda g: "\t- " + g.formula().render(self.__env),
                    self.__pending_goals
                    )) + "\n"
