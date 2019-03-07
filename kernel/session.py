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
    def free(cls, ident):
        assert ident in cls.sessions, "freeing an invalid session %3d" % ident
        del cls.sessions[ident]

    @classmethod
    def get(cls, ident):
        return cls.sessions[ident]

    def __init__(self, ident):
        self.ident = ident
        self.task = None

    def __str__(self):
        return 'Session %3d: %s' % (self.ident, str(self.task))
