from .command import Command

class RewriteCommand(Command):

    class RewriteHint:
        def __init__(self, type: 'Term', pattern: 'Term', lemma: 'Term', right2left: 'bool'):
            self.type = type
            self.pattern = pattern
            self.lemma = lemma
            self.right2left = right2left

    def __init__(self, hints, task=None):
        self.hints = hints
        self.task = task

    def run(self, top):
        top.print('rewriting starts.')
