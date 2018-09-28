class Constant:
    def __init__(self, name: 'str', type: 'Term', body=None, is_builtin=False):
        self.name = name
        self.type = type
        self.body = body
        self.is_builtin=is_builtin

    def __str__(self):
        if self.body is None:
            return "%s: %s" % (self.name, self.type)
        else:
            return "%s: %s := %s" % (self.name, self.type, self.body)


class MutInductive:

    class Constructor:
        def __init__(self, name: 'str', typ: 'Term'):
            self.name = name
            # the reason we use typ instead of type here is a consideration for dependent types
            self.typ = typ

        def type(self, environment=None, context=[]):
            return self.typ

    class Inductive:
        def __init__(self, name: 'str', arity, constructors):
            self.name = name
            self.arity = arity
            self.constructors = constructors

        def type(self, environment=None):
            return self.arity

        def render(self, environment=None):
            return "%s := %s" % (
                    self.type(environment).render(environment),
                    " | ".join(map(lambda c: c.name + ": " + c.type(environment).render(environment), self.constructors))
                    )


    def __init__(self, name: 'str', inds: 'Inductive list', is_builtin=False):
        self.name = name
        self.inds = inds
        self.is_builtin=is_builtin
