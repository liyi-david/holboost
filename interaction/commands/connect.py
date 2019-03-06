from kernel.session import Session

from .command import Command
from .result import DictResult


class ConnectCommand(Command):

    def __init__(self):
        pass

    def run(self, top):
        if 'cache' not in top.namespace:
            # create cache
            top.namespace['cache'] = dict()

        sess = Session.alloc()
        top.print('connection from client [ %s ] from [ %s ], specified session %d' % (
            self.task.client,
            self.task.client_addr[0],
            sess.ident
            )
        )

        # TODO session is important for further parallel optimization
        # here 0 is only a placeholder
        result = { "session" : sess.ident }

        if self.task.client_addr[0] in ('127.0.0.1', 'localhost'):
            # the connection comes from a local client
            pass
        else:
            pass

        return result

    @classmethod
    def from_json(cls, json_item):
        return ConnectCommand()
