from kernel.proofview import Oracle


class BasicOracle(Oracle):

    @classmethod
    def evaluate_goal(cls, g):
        return -1 * g.formula().depth()

    @classmethod
    def evaluate_term(cls, t):
        return 1
