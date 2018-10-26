from kernel.interpretation import Provable

class SmtProvable(Provable):

    def __init__(self, proved_formula):
        Provable.__init__(self)
        self.proved_formula = proved_formula

    def get_proof_obligation(self):
        pass

    def render(self, environment, context=[], debug=False):
        return "<smt-provable hypothesis %s>" % self.proved_formula.render(environment, context, debug)
