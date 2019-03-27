from abc import ABCMeta

class Driver(metaclass=ABCMeta):

    class ExportError(Exception): pass

    @classmethod
    def export(cls, t, environment=None):
        assert cls != Driver
        subclasses = cls.__subclasses__()

        for subclass in subclasses:
            try:
                rel = subclass.export(t, environment)
                if rel is not None:
                    return rel
            except cls.ExportError:
                pass

        raise cls.ExportError
