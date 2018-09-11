class Task:

    def __init__(self, goal, constants={}, context_variables={}):
        self.goal = goal
        self.constants = constants
        self.context_variables = context_variables

    def __str__(self):
        return "The task has %d constants, \n" % len(self.constants) + \
                "[] |- %s" % (str(self.goal))
