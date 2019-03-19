from kernel.macro import Macro, MacroFoldRule
from kernel.term import Ind, Case
from lib.common import code_indent

bool  = Ind('Coq.Init.Datatypes.bool', 0)
true  = bool[0]
false = bool[1]

class Ite(Macro):

    class FoldIte(MacroFoldRule):

        @classmethod
        def fold(cls, term):
            if isinstance(term, Case) and term.term_type == bool:
                return Ite(
                        term.term_matched.fold(),
                        term.cases[0].fold(),
                        term.cases[1].fold()
                        )

            return None


    def __init__(self, cond, thenExpr, elseExpr=None):

        self.cond = cond
        self.thenExpr = thenExpr
        self.elseExpr = elseExpr

    def to_json(self):
        json = Macro.to_json(self)
        json.update({
            'cond': self.cond.to_json(),
            'then': self.thenExpr.to_json(),
            'else': None if self.elseExpr is None else self.elseExpr.to_json()
            })
        return json

    def render(self, environment=None, debug=False):
        return ("if %s then\n" % self.cond.render(environment, debug)) + \
                code_indent(self.thenExpr.render(environment, debug), 1, forceEndl=True) + (
                    "" if self.elseExpr is None else "else\n" + code_indent(self.elseExpr.render(environment, debug), 1, forceEndl=True)
                    )

    def unfold(self):
        assert self.elseExpr is not None, "currently we cannot unfold a if with no else branch"
        # FIXME
        pass
