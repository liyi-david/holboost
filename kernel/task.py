from kernel.environment import Environment

class Task(Environment):

    def __init__(self, goal, constants={}, variables={}, mutinds={}, command=None):
        self.goal = goal
        self.command = command
        Environment.__init__(self, constants, mutinds, variables)

    def __str__(self):
        return "The task has %d constants, %d mut-inductives and %d context variables\n" % (
                len(self.constants),
                len(self.mutinds),
                len(self.variables)
                ) + "[] |- %s" % (self.goal.render(self))
