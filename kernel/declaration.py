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


class Inductive:
    pass
