from .environment import Environment
from .term import Term, Sort
from .tactic import Tactic


class Goal:
    def __init__(self, goal_formula, env=None):
        """
        a goal contains a goal formula and a proof (if the goal is already proved)
        the goal has a corresponding proofview when it is created in a proving process.

        similary with in Coq, all these variables are private, meaning you are not
        supposed to modify them casually (of course you can always do it if you want,
        after all this is Python!).
        """
        self.__formula = goal_formula
        self.__proof = None
        self.__env = env

    def env(self): return self.__env

    def formula(self): return self.__formula

    def give_proof(self, proof):
        # FIXME for now we disable type checking for debugging
        # if proof.type(self.__proofview.env()) != self.__formula:
            # raise TypeError("type mismatch between the goal and the given proof")

        self.__proof = proof

    def closed(self):
        return self.__proof is not None

    def __repr__(self):
        return "<%s Goal: %s>" % ("Closed" if self.closed() else "Pending", self.__formula.render(self.env()))



class Proofview:

    """
    A proofview is used to describe and store the progress of proving a certain formula.
    It follows the concept of proofview in Coq but does not precisely follow its definition.
    """

    def __init__(self, goal_formula, env=None):
        if not isinstance(goal_formula, Term):
            raise TypeError("type of the goal must be a Holboost term.")

        env = env if env is not None else Environment.default()
        if goal_formula.type(env) != Sort.mkProp():
            raise TypeError("only propositions can be proved.")

        self.__goal = goal_formula
        self.__proof = None
        self.__pending_goals = []
        self.__closed_goals = []
        self.__env = env

        self.__pending_goals.append(Goal(goal_formula, self.env()))

        if self.__env is None:
            raise Exception("cannot prove anything with no environment (nor default environment) provided!")

    def auto(self, until=lambda p: False):
        something_done = True
        while not until(self) and something_done and not self.closed():
            # if no tactic works on any pending goal, the process terminates
            something_done = False

            for goal in self.__pending_goals:
                for tactic in Tactic.registered():
                    try:
                        generated_new_goals = tactic.run(goal)
                        assert goal.closed(), "tactic %s finishes with the goal %s still open!" % (
                                tactic.__name__,
                                repr(goal)
                                )

                        if tactic.is_unreliable:
                            # TODO perform post-type-checking
                            pass

                        # append the generated new goals to the queue
                        self.close_goal(goal)
                        for g in generated_new_goals:
                            self.__pending_goals.append(g)

                        break
                    except Tactic.TacticFailure:
                        pass

                if goal.closed():
                    something_done = True
                    break

        return self


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
                    lambda g: "\t- " + g.formula().render(g.env()),
                    self.__pending_goals
                    )) + "\n"
