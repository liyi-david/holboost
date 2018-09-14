class Task:

    def __init__(self, goal, constants={}, context_variables={}, mutinds={}, command=None):
        self.goal = goal
        self.constants = constants
        self.context_variables = context_variables
        self.mutinds = mutinds
        self.command = command

    def __str__(self):
        return "The task has %d constants, %d mut-inductives and %d context variables\n" % (
                len(self.constants),
                len(self.mutinds),
                len(self.context_variables)
                ) + "[] |- %s" % (self.goal.render(self))
