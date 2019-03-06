class Session:

    """ int -> Session """
    sessions = dict()
    ident_next = 0

    @classmethod
    def alloc(cls):
        ident = cls.ident_next
        cls.ident_next += 1
        cls.sessions[ident] = cls(ident)
        return cls.sessions[ident]

    @classmethod
    def get(cls, ident):
        return cls.sessions[ident]

    def __init__(self, ident):
        self.ident = ident
        self.tasks = []

    def __str__(self):
        return 'Session %3d with %3d tasks' % (self.ident, len(self.tasks))
