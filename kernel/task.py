class Task:

    def __init__(self, goal, constants={}, context_variables={}, mutinds={}):
        self.goal = goal
        self.constants = constants
        self.context_variables = context_variables
        self.mutinds = mutinds

    def __str__(self):
        return "The task has %d constants, %d mut-inductives and %d context variables\n" % (
                len(self.constants),
                len(self.mutinds),
                len(self.context_variables)
                ) + "[] |- %s" % (self.goal.export(self))
