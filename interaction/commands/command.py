# this file describe the abstract class of command

import abc

class Command(abc.ABC):

    def __init__(self):
        self.task = None

    @abc.abstractmethod
    def run(self, top: 'Top'):
        pass

