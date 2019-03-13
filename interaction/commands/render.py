from kernel.term import Term, Const
from .command import Command

class RenderCommand(Command):

    rendered = {}

    def __init__(self, term, path):
        Command.__init__(self)

        self.term = term
        # path should be like "a.b.c.d"
        self.path = path


    def run(self, top):
        if self.term is not None:
            if isinstance(self.term, Const):
                self.term = self.term.unfold(self.task)

            termstr = self.term.autofold().render(self.task)
            top.print(termstr)

            paths = self.path.split('.')
            render_ptr = self.rendered

            for token in paths:
                if token not in render_ptr:
                    render_ptr[token] = {}

                render_ptr = render_ptr[token]

            render_ptr['value'] = termstr

    @classmethod
    def from_json(cls, json_item):
        return RenderCommand(Term.from_json(json_item['term']), json_item['path'])
