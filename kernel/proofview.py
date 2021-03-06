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

    def failed(self):
        # a proof is failed once a subgoal is aborted
        return any(map(lambda g: g.aborted(), self.succ_goals))

    def qed(self):
        return all(map(lambda g: a.qed(), self.succ_goals))


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

    def failed(self):
        # an union proof is faileded only when all of its sub-proofs
        # are failed
        return all(map(lambda p: p.failed(), self.proofs))

    def qed(self):
        return any(map(lambda p: p.qed(), self.proofs))

    @property
    def succ_goals(self):
        # FIXME low efficiency
        return sum(map(lambda p: p.succ_goals, self.proofs), [])


class AbortedProof:
    """
    a failed proof contains a partial proof
    """

    def __init__(self, raw_proof):
        self.raw_proof = raw_proof

    def failed(self):
        return True

    def qed(self):
        return False


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
        self.created_by = None

    def env(self): return self.__env

    def formula(self): return self.__formula

    def abort_proof(self):
        self.__proof = AbortedProof(self.__proof)

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

    def proof(self):
        return self.__proof

    def parent(self):
        return self.__parent

    def set_parent(self, parent_goal):
        self.__parent = parent_goal


    def close(self):
        self.__closed = True

    def closed(self):
        return self.__closed

    def proved(self):
        return self.__proof is not None and not isinstance(self.__proof, AbortedProof)

    def qed(self):
        return self.__proof is not None and self.__proof.qed()

    def aborted(self):
        # a goal is labelled `aborted` only when an aborted proof is provided
        # this basically make it easier to manage the different proof queues
        return self.__proof is not None and isinstance(self.__proof, AbortedProof)

    def trace(self):
        p = self
        trace = []
        while p is not None:
            trace.append(p)
            p = p.__parent

        return "\n".join(map(lambda g: repr(g), trace))

    def render(self, *args, **kwargs):
        return self.formula().render(*args, **kwargs)

    def __repr__(self):
        if self.aborted():
            status = "Aborted"
        elif self.closed():
            status = "Closed"
        else:
            status = "Pending"

        str_created_by = "" if self.created_by is None else ", created by " + str(self.created_by)
        return "<%s Goal: %s%s>" % (status, self.__formula.render(self.env()), str_created_by)


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

    class ProofFailed(Exception): pass

    def __init__(self, goal_formula, env=None, oracle=Oracle):
        if not isinstance(goal_formula, Term):
            raise TypeError("the goal-to-prove must be a Holboost term.")

        self.__env = env if env is not None else Environment.default()

        if goal_formula.type(self.__env) != Sort.mkProp():
            raise TypeError("only propositions can be proved.")

        self.__goal = Goal(goal_formula, self.__env)
        self.__proof = None
        self.__pending_goals = []
        self.__proved_goals = []
        self.__aborted_goals = []
        self.__oracle = oracle

        self.__pending_goals.append(self.__goal)

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

                        for g in proof.succ_goals:
                            g.created_by = tactic

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

    def proved_goals(self):
        return tuple(self.__proved_goals)

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
        assert goal in self.__pending_goals or goal in self.__proved_goals


        # close the goal (with no proof give) first
        proof = goal.proof()
        goal.abort_proof()
        goal.close()

        self.__aborted_goals.append(goal)
        if goal in self.__pending_goals:
            self.__pending_goals.remove(goal)
        else:
            self.__proved_goals.remove(goal)


        # close all the subgoals
        if proof is None:
            pass
        elif isinstance(proof, Proof):
            for g in proof.succ_goals:
                if not g.aborted():
                    self.abort_goal(g)
        elif isinstance(proof, UnionProof):
            for subproof in proof.proofs:
                for g in subproof.succ_goals:
                    if not g.aborted():
                        self.abort_goal(g)


        # close the parent goal if needed
        if goal.parent() is not None:
            if not goal.parent().aborted():
                self.try_abort_goal(goal.parent())
        else:
            # every goal has its parents except for the root goal
            # when the root goal is aborted the proofview fails
            assert goal == self.__goal
            raise self.ProofFailed("the proof cannot be finished automatically")

    def try_abort_goal(self, goal):
        # if there is no possibility to prove the goal any more
        # the the goal is aborted

        assert not goal.aborted(), "a goal should not be aborted twice"
        if goal.proof().failed():
            self.abort_goal(goal)

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

            # when a proof does not have any successing goals ...
            # NOTE
            # a proof is completed only when at least one of its successing
            # proofs has no successing goals
            if len(proof.succ_goals) == 0:
                # the proof is finished
                # now we break and close the goal
                self.close_goal(goal)
                self.qed_goal(goal)
                return

            for gl in proof.succ_goals:
                gl.set_parent(goal)

        self.close_goal(goal)

    def qed_goal(self, goal):

        # abort all the unproved subgoals
        proof = goal.proof()
        if isinstance(proof, Proof):
            for g in proof.succ_goals:
                if not g.proved():
                    self.abort_goal(g)
        elif isinstance(proof, UnionProof):
            for subproof in proof.proofs:
                for g in proof.succ_goals:
                    if not g.proved():
                        self.abort_goal(g)
        else:
            assert False

        # check whether the parent goal can be qed
        if goal.parent() is None:
            return
        else:
            if goal.parent().qed():
                self.qed_goal(goal.parent())


    def closed(self):
        return len(self.__pending_goals) == 0

    def env(self): return self.__env

    def __repr__(self):
        if self.closed():
            status = "closed" if len(self.__aborted_goals) == 0 else "failed"
            return "<proofview on %s, %s>" % (
                    self.__goal.formula().render(self.__env),
                    status
                    )
        else:
            return "<proofview on %s, %d goals pending, %d goals closed, %d goals aborted>" % (
                    self.__goal.formula().render(self.__env),
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
                        list(sorted(self.__pending_goals, key=lambda g: self.__oracle.evaluate_goal(g), reverse=True)) +
                        ([] if not debug else (self.__proved_goals + self.__aborted_goals))
                    )) + "\n"
