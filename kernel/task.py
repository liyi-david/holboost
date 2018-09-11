class Task:

    def __init__(self, goal, constants=[]):
        self.goal = goal
        self.constants = constants

    def __str__(self):
        return "The task has %d constants, \n" % len(self.constants) + \
                "[] |- %s" % (str(self.goal))
