class Task:

    def __init__(self, goal, constants={}, context_variables={}, mutinds={}):
        self.goal = goal
        self.constants = constants
        self.context_variables = context_variables
        self.mutinds = mutinds

    def __str__(self):
        return "The task has %d constants, \n" % len(self.constants) + \
                "[] |- %s" % (self.goal.export(self))
