from proving import load
from kernel.environment import Environment
from kernel.dsl import DSL

import traceback


def exec_or_evar(*args):
    try:
        eval_result = eval(*args)
        if eval_result is not None:
            print(eval_result)

        return True
    except SyntaxError:
        pass

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
        cmd = DSL.preprocess(cmd)
        if self.debug_mode:
            return exec_or_evar(cmd, self.namespace, self.debug_namespace)
        else:
            return exec_or_evar(cmd, self.namespace)

    def query(self, name):
        task = None

        if Environment.default() is not None:
            task = Environment.default()

        if 'task' in self.namespace:
            task = self.namespace['task']

        if task is None:
            self.print("neither default environment nor current task is provided.")

        # search constants
        result = []
        filt = lambda n: n.split(".")[-1] == name
        result += task.constant(filt)
        result += task.mutind(filt)
        result += task.variable(filt)

        for item in result:
            self.print(item)


    def load(self, filename):
        with open(filename) as rcfile:
            if self.run(rcfile.read()) is False:
                self.print('failed loading file %s.' % filename)
                return False

        return True

    # =========================================================================

    # store/restore are used to reduce the communication cost. when a client send
    # a task to the server, it copies all the builtin definitions to the cache,
    # which will be stored on a local file and recovered next time when the
    # holboost shell is open

    __local_file = "cache.temp"

    def store(self):
        from pickle import dump
        with open(self.__local_file, "wb") as f:
            dump(self.namespace['cache'], f)

    def restore(self):
        from pickle import load
        from os.path import exists

        if not exists(self.__local_file):
            return

        with open(self.__local_file, "rb") as f:
            try:
                self.namespace['cache'] = load(f)
            except:
                self.print("loading cache failed.")

    # =========================================================================

    def toploop(self):
        # initialization from local database
        self.restore()

        # load rc file
        try:
            print("Loading configurations from .holboostrc ...")
            self.load(".holboostrc")
        except FileNotFoundError:
            pass

        print("Holboost toploop started.")
        multiline_command = ""

        # in two cases, holboost shell jumps to multi-line mode
        #
        # 1. the last non-blank character of the current line is `:`, indicating python starts a code block
        # 2. there is an unclosed `{?`, indicating that the user is typing a DSL fragment

        while True:
            if multiline_command != "":
                # working in multi-line mode
                command = input("\rHolboost ... ")
                if command == "":
                    # run them
                    command = multiline_command
                    multiline_command = ""
                else:
                    multiline_command += command + "\n"
                    command = ""
            else:
                command = input("\rHolboost >>> ")

                # jump to multiline-mode
                if len(command) > 0 and (command.strip()[-1] == ':' or DSL.unclosed_dsl(command)):
                    multiline_command = command + "\n"
                    # do not execute it now
                    command = ""

            try:
                self.run(command)
            except Exception as err:
                # traceback.print_exc()
                # when an exception is triggered by a input command, there is not importance to traceback
                # the full stack
                print(err)

    # ================================= default top ===========================
    __default_top = None

    @classmethod
    def default(cls):
        return cls.__default_top

    @classmethod
    def set_default(cls, top):
        cls.__default_top = top
