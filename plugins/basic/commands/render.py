from kernel.term import Term, Const
from kernel.command import Command

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

            paths = self.path.split('.')
            render_ptr = self.rendered

            for token in paths[:-1]:
                if token not in render_ptr:
                    render_ptr[token] = {}

                render_ptr = render_ptr[token]

            render_ptr[paths[-1]] = self.term.fold().to_json(self.task)
            top.debug('render', self.term.fold().render(self.task))
        else:
            paths = self.path.split('.')
            render_ptr = self.rendered

            for token in paths:
                render_ptr = render_ptr[token]

            top.debug('render', render_ptr)
            return render_ptr

    @classmethod
    def from_json(cls, json_item):
        return RenderCommand(
                None if 'term' not in json_item else Term.from_json(json_item['term']),
                json_item['path']
                )
