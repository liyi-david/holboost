import abc

class Format(abc.ABC):

    @staticmethod
    @abc.abstractmethod
    def export_term(t: 'Term'):
        pass

    @abc.abstractmethod
    def import_term(extenral_t):
        pass

    @abc.abstractclassmethod
    def export_task(t: 'Task'):
        pass

    @abc.abstractclassmethod
    def import_task(external_t: 'Task'):
        pass
