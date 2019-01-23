from kernel.macro import ProofTerm

class SmtSolved(ProofTerm):

    def __init__(self, proved_formula):
        ProofTerm.__init__(self)
        self.proved_formula = proved_formula

    def get_proof_obligation(self):
        pass

    def render(self, environment, debug=False):
        return "<smt-provable hypothesis %s>" % self.proved_formula.render(environment, debug)
