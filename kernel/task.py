from .environment import NamedEnvironment, Environment

from time import time

class Task(NamedEnvironment):

    # the current running task
    # it should be extended to support parallel execution in the future
    # in this case, it may be rewritten as a dict mapping session to tasks
    current = None

    def __init__(self, goal, constants={}, variables={}, mutinds={}, command=None, client=None, client_addr=None):
        NamedEnvironment.__init__(self, constants, mutinds, variables)

        self.goal = goal
        self.command = command
        self.client = client
        self.client_addr = client_addr

        if self.command is not None:
            self.command.task = self

    def __str__(self):
        return "The task has %d constants, %d mut-inductives and %d context variables." % (
                len(self.constants()),
                len(self.mutinds()),
                len(self.variables())
                )

    @staticmethod
    def get_current():
        return Task.current

    def set_current(self):
        Task.current = self
        Environment.set_external_default(self)

    @classmethod
    def from_json(cls, json_item):
        from .term import Term
        from interaction.commands import Command
        env = Environment.from_json(json_item)

        task = Task(
                None if 'goal' not in json_item else Term.from_json(json_item['goal']),
                env.constants,
                env.variables,
                env.mutinds,
                Command.from_json(json_item['command'])
                )


        return task

    def run(self, top):
        if self.command is not None:
            t_start = time()
            self.set_current()
            result = self.command.run(top)
            t_total = time() - t_start
            top.print("command %s finished in %.6f seconds." % (type(self.command), t_total))
            return result
        else:
            raise Exception("command is missing")
