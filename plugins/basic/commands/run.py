from kernel.session import Session
from kernel.command import Command


class RunCommand(Command):
    """
    run command let a client run any python commands on the server side. this should be strictly disabled when
    the client is running on a different machine and not authorized

    TODO authorization mechanism?
    """
    def __init__(self, cmd):
        Command.__init__(self)
        self.cmd = cmd

    @classmethod
    def from_json(cls, json_item):
        return RunCommand(json_item['command'])

    def run(self, top):
        if not self.task.client_addr[0] in ("127.0.0.1", "localhost"):
            msg = "Authorization failure, only local clients can run arbitrary python command."
            return msg

        try:
            copied_ns = top.namespace.copy()
            copied_ns ['__task__'] = self.task
            top.run(self.cmd, copied_ns)
            return "successfully finished."
        except Exception as err:
            from traceback import print_exc
            print_exc()
            raise err
