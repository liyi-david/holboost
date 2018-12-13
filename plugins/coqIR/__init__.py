from kernel.macro import Macro
from kernel.term import Lambda, Var


class Statement(Macro):

    def __repr__(self):
        return self.render()

    def unfold(self):
        raise Exception('unimplemented')


class Assign(Statement):

    def __init__(self, name, expr, typ=None):
        self.name = name
        self.expr = expr
        self.typ = typ if typ is not None else expr.type()

    def render(self, environment=None, debug=False):
        if self.name is not None:
            return "%s ← %s" % (self.name, self.expr.render(environment, debug))
        else:
            return self.expr.render(environment, debug)

    def unfold(self):
        raise Macro.MacroAbuse("cannot unfold a single assign statement!")

    def to_json(self):
        json = Statement.to_json(self)
        json.update({
                "name": self.name,
                "type": self.typ.to_json(),
                "value": self.expr.to_json()
                })

        return json


class Return(Statement):

    def __init__(self, val):
        self.val = val

    def render(self, environment=None, debug=False):
        return "return %s" % self.val.render(environment, debug)

    def unfold(self):
        pass

    def to_json(self):
        json = Statement.to_json(self)
        json.update({
            "return_value": self.val.to_json()
            })

        return json


class Sequential(Statement):

    def __init__(self, stmts=[]):
        self.stmts = stmts

    def render(self, environment=None, debug=False):
        return "\n".join(
                map(lambda stmt: stmt.render(environment, debug), self.stmts)
                )

    def unfold(self):
        pass

    def to_json(self):
        json = Statement.to_json(self)
        json.update({
            "statements": [ stmt.to_json() for stmt in self.stmts ]
            })

        return json


print('coqIR, ', end='')
