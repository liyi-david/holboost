from kernel.term import Construct, Ind


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
            self.ind = None

        def type(self, environment=None, context=[]):
            return self.typ.rels_subst([self.ind.as_term()])

    class Inductive:
        def __init__(self, name: 'str', arity, constructors):
            self.name = name
            self.arity = arity
            self.mutind = None
            self.constructors = constructors
            for c in self.constructors:
                c.ind = self

        def as_term(self):
            return Ind(self.mutind.name, self.mutind.inds.index(self))

        def type(self, environment=None, context=[]):
            return self.arity

        def render(self, environment=None):
            return "%s := \n%s" % (
                    self.type(environment).render(environment),
                    "\n| ".join(map(lambda c: c.name + ": " + c.type(environment).render(environment), self.constructors))
                    )


    def __init__(self, name: 'str', inds: 'Inductive list', is_builtin=False):
        self.name = name
        self.inds = inds
        for i in self.inds:
            i.mutind = self
        self.is_builtin=is_builtin
