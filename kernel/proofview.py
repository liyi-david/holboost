from .environment import Environment
from .term import Term, Sort
from .tactic import Tactic

from math import inf

# FIXME use PriorityQueue in __pending_goals
from queue import PriorityQueue


class Proof:
    def __init__(self, proof_formula, *succ_goals):
        self.proof_formula = proof_formula
        self.succ_goals = list(succ_goals)


class UnionProof:
    """
    a union proof contains a set of sub-proofs that targets on the same goal. Finishing
    any single proof in the sub-proof set will close the goal with current proof.

    FIXME: as a consequent, a goal which is proved by a union proof may not be "CLOSED"
    since there is still chances to extend the proof, e.g. to prove \exists a, a >= 2,
    we can prove 1 >= 2, or 2 >= 2 or 3 >= 2, etc.

    union proofs are NOT NESTED!
    """
    def __init__(self, *proofs):
        self.proofs = proofs


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

        # NOTE only a proofview instance is supposed to call this method

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

    def step(self, until=lambda p: False): return self.auto(until=until, bound=1)

    def auto(self, until=lambda p: False, bound=inf):
        something_done = True
        steps = 0

        while not until(self) and something_done and not self.closed() and steps < bound:
            # if no tactic works on any pending goal, the process terminates
            something_done = False
            steps += 1

            for goal in self.__pending_goals:
                for tactic in Tactic.registered():
                    try:
                        proof = tactic.run(goal)
                        self.close_goal_with_proof(goal, proof)
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

    def close_goal_with_proof(self, goal, proof):
        assert goal in self.__pending_goals
        assert not goal.closed()

        if isinstance(proof, Proof):
            self.__pending_goals += proof.succ_goals
        elif isinstance(proof, UnionProof):
            assert False, "unimplemented"
        else:
            raise Exception("unsupported proof type : %s" % type(proof))

        goal.give_proof(proof)
        self.close_goal(goal)

    def closed(self):
        return len(self.__pending_goals) == 0

    def env(self): return self.__env

    def __repr__(self):
        if self.closed():
            return "<proofview on %s, closed>" % (
                    self.__goal.render(self.__env)
                    )
        else:
            return "<proofview on %s, %d goals pending, %d goals closed>" % (
                    self.__goal.render(self.__env),
                    len(self.__pending_goals),
                    len(self.__closed_goals)
                    )

    def __str__(self):
        if self.closed():
            return repr(self)
        else:
            return repr(self) + "\n\n" + "\n".join(map(
                    lambda g: "\t- " + g.formula().render(g.env()),
                    self.__pending_goals
                    )) + "\n"
