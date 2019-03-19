from kernel.command import Command

class IdleCommand(Command):
    @classmethod
    def from_json(cls, json_item):
        return cls()

    def run(self, top):
        top.debug('warning: no command name specified, running IdleCommand instead')
