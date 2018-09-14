from .command import Command

class IdleCommand(Command):
    def run(self, top):
        top.print('No command specified.')
