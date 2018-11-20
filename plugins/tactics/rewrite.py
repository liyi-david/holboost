from kernel.macro import Proof

class RewriteProof(Proof):

    def __init__(self):
        Proof.__init__(self)

    def __repr__(self):
        return "<%s proved by rewriting>" % (self.proved_formula)
