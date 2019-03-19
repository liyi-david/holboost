from kernel.session import Session
from kernel.command import Command


class DisconnectCommand(Command):

    def __init__(self, session_id):
        self.session_id = session_id

    def run(self, top):
        Session.free(self.session_id)
        top.print("session %d is disconnected." % self.session_id)
        return None

    @classmethod
    def from_json(cls, json_item):
        assert 'session' in json_item, "disconnecting command must contain session id"
        return cls(int(json_item['session']))
