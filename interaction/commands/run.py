from .command import Command
from sys import stdout

class RunCommand(Command):
    """
    run command let a client run any python commands on the server side. this should be strictly disabled when
    the client is running on a different machine and not authorized

    TODO authorization mechanism?
    """
    def __init__(self, cmd):
        Command.__init__(self)
        self.cmd = cmd

    def from_json(self, json_item):
        return RunCommand(json_item['command'])

    def run(self, top):
        try:
            top.run(self.cmd)
            return "successfully finished."
        except Exception as err:
            from traceback import print_exc
            print_exc()
            return "failed because %s" % str(err)
