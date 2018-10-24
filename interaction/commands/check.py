from .command import Command

class CheckCommand(Command):
    """
    Check command is used to print or check a term or a reference (constant, mutind, etc.)
    """
    def __init__(self, id, term):
        Command.__init__(self)

        self.id = id
        self.term = term
        assert id is None or term is None

    def run(self, top):
        if self.term is not None:
            termstr = "%s :\n\t%s" % (
                    self.term.render(self.task),
                    self.term.type(self.task).render(self.task),
                    )
            top.print(self.term.type(self.task).render(self.task))
        else:
            termstr = "%s not found!" % self.id
            dotid = "." + self.id
            id = self.id

            for key in self.task.constants:
                if key.endswith(dotid):
                    termstr = str(self.task.constants[key].body)
                    break

            for key in self.task.mutinds:
                if key.endswith(dotid):
                    termstr = str(self.task.mutinds[key])
                    break

            for key in self.task.variables:
                if key == self.id:
                    termstr = str(self.task.variables[key].type)
                    break

            top.print(termstr)
            termstr = "%s :=\n\t%s" % (
                    id, termstr
                    )

        return termstr
