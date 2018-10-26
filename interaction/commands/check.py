from .command import Command

class CheckCommand(Command):
    """
    Check command is used to print or check a term or a reference (constant, mutind, etc.)
    """
    def __init__(self, id, term, fullcheck=False):
        Command.__init__(self)

        self.id = id
        self.term = term
        self.fullcheck = fullcheck
        assert id is None or term is None

    def run(self, top):
        if self.term is not None:
            termstr = self.term.render(self.task)
            if self.fullcheck:
                typ, sideff = self.term.check(self.task)

                returnstr = "\n%s :\n\n\t%s\n\nuniverse constraints:\n\n\t%s" % (
                        termstr,
                        typ.render(self.task),
                        str(sideff)
                        )
            else:
                typestr = self.term.type(self.task).render(self.task)
                returnstr = "\n%s :\n\n\t%s" % (
                        termstr,
                        typestr
                        )

            top.print(returnstr)
        else:
            returnstr = "%s not found!" % self.id
            dotid = "." + self.id
            id = self.id

            for key in self.task.constants:
                if key.endswith(dotid):
                    returnstr = str(self.task.constants[key].body)
                    break

            for key in self.task.mutinds:
                if key.endswith(dotid):
                    returnstr = str(self.task.mutinds[key])
                    break

            for key in self.task.variables:
                if key == self.id:
                    returnstr = str(self.task.variables[key].type)
                    break

            top.print(returnstr)
            returnstr = "%s :=\n\t%s" % (
                    id, returnstr
                    )

        return returnstr
