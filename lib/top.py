from proving import load

import traceback

def exec_or_evar(*args):
    try:
        eval_result = eval(*args)
        if eval_result is not None:
            print(eval_result)
    except SyntaxError:
        exec(*args)


class Top:

    def __init__(self):
        self.namespace = load()
        self.supported_methods = self.namespace.keys()
        self.message_pool = []
        self.namespace['list'] = (lambda: print(self.supported_methods))
        self.namespace['log'] = (lambda: print("\n".join(self.message_pool[-5:])))

    def log_message(self, message):
        self.message_pool.append(message)

    def print(self, *args):
        print("\rCommand MSG ", *args)
        print("Holboost >>> ", end="", flush=True)

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
