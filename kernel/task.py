from kernel.environment import Environment

class Task(Environment):

    def __init__(self, goal, constants={}, variables={}, mutinds={}, command=None, client=None):
        self.goal = goal
        self.command = command
        self.client = client
        if self.command is not None:
            self.command.task = self

        Environment.__init__(self, constants, mutinds, variables)

    def __str__(self):
        return "The task has %d constants, %d mut-inductives and %d context variables\n" % (
                len(self.constants),
                len(self.mutinds),
                len(self.variables)
                ) + "[] |- %s" % (self.goal.render(self))

    def run(self, top):
        if self.command is not None:
            return self.command.run(top)
        else:
            raise Exception("command is missing")
