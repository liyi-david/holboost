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
                str_sideff = "\n".join(map(lambda uc: "\t" + str(uc), list(sideff)))

                returnstr = "\n%s :\n\n\t%s\n" % (
                        termstr,
                        typ.render(self.task),
                        )

                if len(sideff) > 0:
                    returnstr += "\nuniverse constraints:\n\n%s\n" % str_sideff
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

            for key in self.task.constants():
                if key.endswith(dotid):
                    returnstr = str(self.task.constant(key).body)
                    break

            for key in self.task.mutinds():
                if key.endswith(dotid):
                    returnstr = str(self.task.mutind(key))
                    break

            for key in self.task.variables():
                if key == self.id:
                    returnstr = str(self.task.variable(key).type(self.task))
                    break

            top.print(returnstr)
            returnstr = "%s :=\n\t%s" % (
                    id, returnstr
                    )

        return returnstr
