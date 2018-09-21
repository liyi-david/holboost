# this file describe the abstract class of command

import abc

class Command(abc.ABC):

    @abc.abstractmethod
    def run(self, top: 'Top'):
        pass

