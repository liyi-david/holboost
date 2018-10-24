from kernel.environment import Environment
from time import time

class Task(Environment):

    # the current running task
    # it should be extended to support parallel execution in the future
    # in this case, it may be rewritten as a dict mapping session to tasks
    current = None

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
                ) + "[] |- %s" % ("None" if self.goal is None else self.goal.render(self))

    def run(self, top):
        if self.command is not None:
            t_start = time()
            Task.current = self
            result = self.command.run(top)
            t_total = time() - t_start
            top.print("command %s finished in %.6f seconds." % (type(self.command), t_total))
            return result
        else:
            raise Exception("command is missing")
