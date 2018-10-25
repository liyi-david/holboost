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
        self.debug_namespace = {}
        self.supported_methods = self.namespace.keys()
        self.message_pool = []
        self.debug_mode = False

        # initalization of the namespace
        self.namespace['list'] = (lambda: print(self.supported_methods))
        self.namespace['log'] = (lambda: print("\n".join(self.message_pool[-5:])))
        self.namespace['load'] = (lambda f: self.load(f))
        self.namespace['query'] = (lambda s: self.query(s))
        self.namespace['cache'] = {}
        self.namespace['debug'] = self.activate_debug
        self.namespace['top'] = self

        self.debug_modules = set()

    def activate_debug(self, *modules):
        self.print("the following modules have been added to the debug list: %s" % str(modules))
        self.debug_modules = self.debug_modules.union(set(modules))
        self.debug_mode = True

    def log_message(self, message):
        self.message_pool.append(message)

    def print(self, *args):
        print("\rCommand MSG ", *args)
        print("Holboost >>> ", end="", flush=True)

    def debug(self, module, *args):
        if module in self.debug_modules:
            print("\rDebug   MSG ", *args)
            print("Holboost >>> ", end="", flush=True)

    def run(self, cmd):
        exec_or_evar(cmd, self.namespace, self.debug_namespace)

    def query(self, string):
        if 'task' not in self.namespace:
            self.print('no task specified.')
        else:
            task = self.namespace['task']

            # search constants
            for name in task.constants:
                if name.endswith(string):
                    self.print(name, ": ", task.constants[name].type.render(task))

            # search variables
            for name in task.variables:
                if name.endswith(string):
                    self.print(name, ": ", task.variables[name].type.render(task))

            # search mutinds
            for mutind in task.mutinds.values():
                for ind in mutind.inds:
                    if ind.name.endswith(string):
                        self.print(ind.name, ": ", ind.render(task))

    def load(self, filename):
        with open(filename) as rcfile:
            for line in rcfile:
                if self.debug_mode:
                    self.run(line)
                else:
                    self.run(line)

    def toploop(self):
        # load rc file
        try:
            print("Loading configurations from .holboostrc ...")
            self.load(".holboostrc")
        except FileNotFoundError:
            pass

        print("Holboost toploop started.")
        while True:
            command = input("\rHolboost >>> ")
            try:
                if self.debug_mode:
                    self.run(command)
                else:
                    self.run(command)
            except Exception as err:
                traceback.print_exc()
