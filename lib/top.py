from proving import load

import traceback

def exec_or_evar(*args):
    try:
        eval_result = eval(*args)
        if eval_result is not None:
            print(eval_result)
    except KeyboardInterrupt:
        print('command interrupted by user.')
    except SyntaxError:
        exec(*args)


class Top:

    def __init__(self):
        self.namespace = load()
        self.supported_methods = self.namespace.keys()
        self.message_pool = []

        # initalization of the namespace
        self.namespace['list'] = (lambda: print(self.supported_methods))
        self.namespace['log'] = (lambda: print("\n".join(self.message_pool[-5:])))
        self.namespace['query'] = (lambda s: self.query(s))
        self.namespace['cache'] = {}

    def log_message(self, message):
        self.message_pool.append(message)

    def print(self, *args):
        print("\rCommand MSG ", *args)
        print("Holboost >>> ", end="", flush=True)

    def query(self, string):
        if 'task' not in self.namespace:
            self.print('no task specified.')
        else:
            task = self.namespace['task']

            # search constants
            for name in task.constants:
                if name.endswith(string):
                    self.print(name, ": ", task.constants[name].type.render(task))

            # search mutinds
            for mutind in task.mutinds.values():
                for ind in mutind.inds:
                    if ind.name.endswith(string):
                        self.print(ind.name, ": ", ind.render(task))

    def run(self):
        # load rc file
        try:
            with open(".holboostrc") as rcfile:
                print("Loading configurations from .holboostrc ...")
                for line in rcfile:
                    exec_or_evar(line, self.namespace)
        except FileNotFoundError:
            pass

        print("Holboost toploop started.")
        while True:
            command = input("Holboost >>> ")
            try:
                exec_or_evar(command, self.namespace)
            except Exception as err:
                traceback.print_exc()
