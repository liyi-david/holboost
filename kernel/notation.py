import abc
import .term

class Notation(abc.ABC):

    notations = dict()

    @staticmethod
    def register(notation:'Notation') -> 'NoneType':
        Notation.notations[notation.id] = notation

    def unregister(notation: 'Notation') -> 'NoneType':
        del Notation.notations[notation.id]

    @abc.abstractmethod
    def parse(self, raw:str) -> term.Term:
        pass
