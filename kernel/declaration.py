class Constant:
    def __init__(self, name: 'str', type: 'Term', body=None):
        self.name = name
        self.type = type
        self.body = body

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

        def type(self, environment=None):
            return self.typ

    class Inductive:
        def __init__(self, name: 'str', arity, constructors):
            self.name = name
            self.arity = arity
            self.constructors = constructors

        def type(self, environment=None):
            return self.arity


    def __init__(self, name: 'str', inds: 'Inductive list'):
        self.name = name
        self.inds = inds
