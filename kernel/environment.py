class Environment:
    def __init__(self, constants={}, mutinds={}, variables={}):
        self.constants = constants
        self.mutinds = mutinds
        self.variables = variables

    def get_builtins(self):
        builtins = Environment()

        for name in self.constants:
            if self.constants[name].is_builtin:
                builtins.constants[name] = self.constants[name]

        for name in self.mutinds:
            if self.mutinds[name].is_builtin:
                builtins.mutinds[name] = self.mutinds[name]


        return builtins

    def __iadd__(self, env):
        assert isinstance(env, Environment)
        self.constants.update(env.constants)
        self.mutinds.update(env.mutinds)

        return self

    def __repr__(self):
        return str(self)

    def __str__(self):
        return "<holboost environment with %d constants, %d mut-inductives and %d variables>" % (len(self.constants), len(self.mutinds), len(self.variables))
