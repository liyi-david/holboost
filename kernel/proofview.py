from .environment import Environment
from .term import Term, Sort
from .tactic import Tactic

from abc import ABCMeta
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
        # tuples are immutable ...
        self.proofs = list(proofs)

    def append(self, *proofs):
        self.proofs += proofs


class Goal:
    def __init__(self, goal_formula, env=None, parent=None):
        """
        A goal contains a goal formula and a proof (if the goal is already proved)
        the goal has a corresponding proofview when it is created in a proving process.

        Similary with in Coq, all these variables are private, meaning you are not
        supposed to modify them casually (of course you can always do it if you want,
        after all this is Python!).

        A goal may be generated during solving another goal. In this case the goal itself
        usually become part of the proof of another goal, which is called `parent` goal.
        """
        self.__formula = goal_formula
        self.__proof = None
        self.__env = env
        self.__parent = parent
        self.__closed = False

    def env(self): return self.__env

    def formula(self): return self.__formula

    def give_proof(self, proof):
        # FIXME for now we disable type checking for debugging
        # if proof.type(self.__proofview.env()) != self.__formula:
            # raise TypeError("type mismatch between the goal and the given proof")

        # NOTE only a proofview instance is supposed to call this method
        proofs = proof.proofs if isinstance(proof, UnionProof) else [ proof ]
        if self.__proof is None:
            self.__proof = proof
        elif isinstance(self.__proof, UnionProof):
            # ther are already more than one proofs
            self.__proof.append(proofs)
        else:
            # there is only a single proof
            self.__proof = UnionProof(self.__proof, *proofs)

    def set_parent(self, parent_goal):
        self.__parent = parent_goal


    def close(self):
        self.__closed = True

    def closed(self):
        return self.__closed

    def proved(self):
        return self.__proof is not None

    def trace(self):
        p = self
        trace = []
        while p is not None:
            trace.append(p)
            p = p.__parent

        return "\n".join(map(lambda g: g.formula().render(g.env()), trace))

    def __repr__(self):
        if self.__closed:
            if self.__proof is None:
                status = "Aborted"
            else:
                status = "Closed"
        else:
            status = "Pending"

        return "<%s Goal: %s>" % (status, self.__formula.render(self.env()))


class Oracle(metaclass=ABCMeta):

    class OracleFailure(Exception):
        pass

    @classmethod
    def evaluate_goal(cls, g):
        raise cls.OracleFailure("you need to manually specify an oracle or do it in .holboostrc.local")

    @classmethod
    def evaluate_term(cls, t):
        raise cls.OracleFailure("you need to manually specify an oracle or do it in .holboostrc.local")


class Proofview:

    """
    A proofview is used to describe and store the progress of proving a certain formula.
    It follows the concept of proofview in Coq but does not precisely follow its definition.
    """

    def __init__(self, goal_formula, env=None, oracle=Oracle):
        if not isinstance(goal_formula, Term):
            raise TypeError("the goal-to-prove must be a Holboost term.")

        env = env if env is not None else Environment.default()
        if goal_formula.type(env) != Sort.mkProp():
            raise TypeError("only propositions can be proved.")

        self.__goal = goal_formula
        self.__proof = None
        self.__pending_goals = []
        self.__proved_goals = []
        self.__aborted_goals = []
        self.__env = env
        self.__oracle = oracle

        self.__pending_goals.append(Goal(goal_formula, self.env()))

        if self.__env is None:
            raise Exception("cannot prove anything with no environment (nor default environment) provided!")

    def step(self, until=lambda p: False): return self.auto(until=until, bound=1)

    def auto(self, until=lambda p: False, bound=inf):
        """
        auto function tries to solve the goal with no human interaction.
        unlike coq, isabelle, etc. holboost is designed to solve the puzzles
        automatically. in other words, all the design should be good for
        automation instead of human interaction. if something must be done
        manually, it should be done in the coq part before holboost is called,
        or alfter holboost fails and exits.

        well of course, we still need to debug ...
        """
        something_done = True
        steps = 0

        while not until(self) and something_done and not self.closed() and steps < bound:
            # if no tactic works on any pending goal, the process terminates
            something_done = False
            steps += 1

            # FIXME for performance issue, we should not embedded such a un-optimized sorting
            # process in a for-loop
            for goal in sorted(self.__pending_goals, key=lambda g: self.__oracle.evaluate_goal(g), reverse=True):
                # we always choose the goal with higher evaluation to work on

                proofs = []
                for tactic in Tactic.registered():
                    try:
                        # try to create a new proof
                        proof = tactic.run(goal)
                        assert isinstance(proof, Proof), "invalid proof given by tactic %s" % str(tactic)
                        proofs.append(proof)
                    except Tactic.TacticFailure:
                        pass

                if len(proofs) > 0:
                    something_done = True
                    # we can solve this goal .. for now :)
                    self.close_goal_with_proofs(goal, *proofs)
                    break
                else:
                    # never waste time on this goal in the future
                    self.abort_goal(goal)

        return self


    def pending_goals(self):
        return tuple(self.__pending_goals)

    def aborted_goals(self):
        return tuple(self.__aborted_goals)

    def close_goal(self, goal):
        """
        close a goal that already has a proof
        """
        assert goal in self.__pending_goals, "somehow the goal is not in the pending list"

        goal.close()
        self.__pending_goals.remove(goal)
        self.__proved_goals.append(goal)

    def abort_goal(self, goal):
        """
        abort a goal. it may affect its parent goals
        """
        assert goal in self.__pending_goals

        goal.close()
        self.__aborted_goals.append(goal)
        self.__pending_goals.remove(goal)

    def close_goal_with_proofs(self, goal, *proofs):
        """
        close an unproved goal with a proof
        """
        assert goal in self.__pending_goals
        assert not goal.closed()
        assert len(proofs) > 0

        for proof in proofs:
            goal.give_proof(proof)
            self.__pending_goals += proof.succ_goals
            for gl in proof.succ_goals:
                gl.set_parent(goal)

        self.close_goal(goal)

    def closed(self):
        return len(self.__pending_goals) == 0

    def env(self): return self.__env

    def __repr__(self):
        if self.closed():
            status = "closed" if len(self.__aborted_goals) == 0 else "failed"
            return "<proofview on %s, %s>" % (
                    self.__goal.render(self.__env),
                    status
                    )
        else:
            return "<proofview on %s, %d goals pending, %d goals closed, %d goals aborted>" % (
                    self.__goal.render(self.__env),
                    len(self.__pending_goals),
                    len(self.__proved_goals),
                    len(self.__aborted_goals)
                    )

    def __str__(self):
        return self.render()

    def debug(self):
        return self.render(debug=True)

    def render(self, debug=False):

        def get_symbol(g):
            if g.closed() and g.proved():
                return '✔'
            elif g.closed():
                return '✖'
            else:
                return '◔'

        if self.closed() and debug is False:
            return repr(self)
        else:
            return repr(self) + "\n\n" + "\n".join(map(
                    lambda g: "\t" + get_symbol(g) + ' ' + g.formula().render(g.env()),
                    self.__pending_goals + ([] if not debug else (self.__proved_goals + self.__aborted_goals))
                    )) + "\n"
