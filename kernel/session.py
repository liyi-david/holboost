import threading

class Session:

    """ int -> Session """
    sessions = dict()

    @classmethod
    def get(cls):
        if threading.get_ident() not in cls.sessions:
            cls.sessions[threading.get_ident()] = Session()

        return cls.sessions[threading.get_ident()]


    def __init__(self, parent: 'Session'=None) -> 'Declaration | Definition':
        self.threadId = threading.get_ident()
        self.parent = None
        self.namespace = dict()

    def __contains__(self, key):
        return key in self.namespace

    def __get__(self, key):
        return self.namespace[key]

    def __set__(self, key, value):
        assert key not in self
        self.namespace[key] = value
