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
        def __init__(self, name: 'str'):
            self.name = name

    class Inductive:
        def __init__(self, name: 'str', constructors):
            self.name = name
            self.constructors = constructors

    def __init__(self, name: 'str', inds: 'Inductive list'):
        self.name = name
        self.inds = inds
