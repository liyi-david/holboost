from .command import Command
from .result import DictResult

class ConnectCommand(Command):

    def __init__(self):
        pass

    def run(self, top):
        if 'cache' not in top.namespace:
            # create cache
            top.namespace['cache'] = dict()

        top.print('connection from client [ %s ]' % self.task.client)

        # TODO session is important for further parallel optimization
        # here 0 is only a placeholder
        return { "session": 0 }

    @classmethod
    def from_json(cls, json_item):
        return ConnectCommand()
