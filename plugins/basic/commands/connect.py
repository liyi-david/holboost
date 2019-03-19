from kernel.session import Session
from kernel.command import Command

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

        # session id is used to maintain and inherit task content
        if self.task.client in top.namespace['cache']:
            self.task.inherited_environment = top.namespace['cache'][self.task.client]

        sess.task = self.task
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
