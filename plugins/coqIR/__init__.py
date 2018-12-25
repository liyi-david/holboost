from kernel.macro import Macro
from kernel.term import Lambda, Var, Const, Apply


class Statement(Macro):

    def __repr__(self):
        return self.render()

    def unfold(self):
        raise Exception('unimplemented')


class Labelled(Macro):
    ut_stmt_label = "src.type.stmt_label"

    @classmethod
    def fold(cls, t):
        if isinstance(t, Apply) and isinstance(t.func, Const) and t.func.name == cls.ut_stmt_label:
            return t.args[2].fold()


class PlaceHolder(Statement):

    ut_placeholder = "src.type.WP_PLACEHOLDER"

    def __init__(self):
        # FIXME name
        self.name = ""

    def render(self, environment=None, debug=False):
        return "{ %s }" % self.name

    @classmethod
    def fold(cls, t):
        if isinstance(t, Apply) and isinstance(t.func, Const) and t.func.name == cls.ut_placeholder:
            return cls()


class Assign(Statement):

    def __init__(self, name, expr, typ=None):
        self.name = name
        self.expr = expr

        try:
            self.typ = typ if typ is not None else expr.type()
        except:
            # FIXME
            self.typ = None

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

    ut_return = "src.type.ret"

    def __init__(self, val):
        self.val = val

    def render(self, environment=None, debug=False):
        return "return %s" % self.val.render(environment, debug)

    def unfold(self):
        pass

    @classmethod
    def fold(cls, t):
        if isinstance(t, Apply) and isinstance(t.func, Const) and t.func.name == cls.ut_return:
            return Return(t.args[4].fold())

    def to_json(self):
        json = Statement.to_json(self)
        json.update({
            "return_value": self.val.to_json()
            })

        return json


class Sequential(Statement):

    ut_bind = "src.type.bind"

    def __init__(self, stmts=[]):
        self.stmts = stmts

    def render(self, environment=None, debug=False):
        return "\n".join(
                map(lambda stmt: stmt.render(environment, debug), self.stmts)
                )

    def unfold(self):
        pass

    @classmethod
    def fold(cls, t):
        stmt = []
        while isinstance(t, Apply) and \
                isinstance(t.func, Const) and t.func.name == cls.ut_bind and \
                isinstance(t.args[4], Lambda):
                    stmt.append(Assign(t.args[4].arg_name, t.args[3].fold()))
                    t = t.args[4].body
        else:
            if len(stmt) == 0:
                return None
            else:
                stmt.append(t.fold())


    def to_json(self):
        json = Statement.to_json(self)
        json.update({
            "statements": [ stmt.to_json() for stmt in self.stmts ]
            })

        return json


print('coqIR, ', end='')
Sequential.register()
Labelled.register()
Return.register()
PlaceHolder.register()
