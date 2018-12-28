from kernel.macro import Macro
from kernel.environment import ContextEnvironment
from kernel.term import Lambda, Var, Const, Apply, Binding, Rel

from plugins.theories.product import tuple


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
            return t.args[2].autofold()


class PlaceHolder(Statement):

    ut_placeholder = "src.type.WP_PLACEHOLDER"

    def __init__(self, name=""):
        self.name = name

    def render(self, environment=None, debug=False):
        return "{ %s }" % self.name

    @classmethod
    def fold(cls, t):
        if isinstance(t, Apply) and isinstance(t.func, Const) and t.func.name == cls.ut_placeholder:
            return cls(t.args[3].autofold())


class Assign(Statement):

    def __init__(self, name, expr, typ=None):
        self.name = name
        self.expr = expr

        # type is not evaluated unless it needs type checking
        self.typ = typ

    def render(self, environment=None, debug=False):
        if isinstance(self.expr, Return):
            str_expr = self.expr.val.render(environment, debug)
        else:
            str_expr = self.expr.render(environment, debug)

        if self.name is not None:
            return "%s ← %s" % (self.name, str_expr)
        else:
            return str_expr

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


class Guard(Statement):

    def __init__(self, expr, typ):
        self.expr = expr
        self.typ = typ

    def render(self, environment=None, debug=False):
        return "// GUARD %s : %s" % (
                self.expr.render(environment, debug),
                self.typ.render(environment, debug)
                )

    @classmethod
    def fold(cls, t):
        _ut_guard = Const('src.type.GUARD')

        if isinstance(t, Apply) and t.func == _ut_guard:
            return cls(t.args[4], t.args[3])


class Return(Statement):

    ut_return = "src.type.ret"

    def __init__(self, val):
        self.val = val

    def render(self, environment=None, debug=False):
        return "return %s" % self.val.render(environment, debug)

    def unfold(self):
        return Apply(
                    Lambda(
                        'r', None,
                        Lambda('s', None, tuple(Rel(1), Rel(0)))
                        ),
                    self.val.unfold(),
                    )

    @classmethod
    def fold(cls, t):
        if isinstance(t, Apply) and isinstance(t.func, Const) and t.func.name == cls.ut_return:
            return Return(t.args[4].autofold())

    def to_json(self):
        json = Statement.to_json(self)
        json.update({
            "return_value": self.val.to_json()
            })

        return json


class Sequential(Statement):

    ut_bind = Const("src.type.bind")

    def __init__(self, *stmts):
        self.stmts = stmts

    def render(self, environment=None, debug=False):
        str_stmts = []
        env = environment
        for stmt in self.stmts:
            str_stmts.append(stmt.render(env, debug))
            if isinstance(stmt, Assign):
                env = ContextEnvironment(Binding(stmt.name, stmt.expr), env)

        return "\n".join(str_stmts)

    def unfold(self):
        if isinstance(self.stmts[0], Assign):
            return Apply(
                    self.ut_bind,
                    self.stmts[0].expr.unfold(),
                    Lambda(self.stmts[0].name, self.stmts[0].typ, Sequential(*self.stmts[1:]).unfold()),
                    )
        elif isinstance(self.stmts[0], Return):
            return self.stmts[0].unfold()
        else:
            assert False, "unrecognized head statement %s in a sequential composition" % self.stmts[0]

    @classmethod
    def fold(cls, t):
        stmts = []
        while isinstance(t, Apply) and t.func == cls.ut_bind and isinstance(t.args[4], Lambda):
            stmts.append(Assign(t.args[4].arg_name, t.args[3].autofold()))
            t = t.args[4].body

        else:
            if len(stmts) == 0:
                return None
            else:
                stmts.append(t.autofold())

        return Sequential(*stmts)

    def to_json(self):
        json = Statement.to_json(self)
        json.update({
            "statements": [ stmt.to_json() for stmt in self.stmts ]
            })

        return json


Sequential.register()
Labelled.register()
Return.register()
Guard.register()
PlaceHolder.register()
