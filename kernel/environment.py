
class Environment:

    __default_environment = None
    __external_default_environment = None

    @classmethod
    def set_default(cls, env):
        assert isinstance(env, cls)
        cls.__default_environment = env

    @classmethod
    def default(cls):
        if cls.__default_environment is None and cls.__external_default_environment is not None:
            return cls.__external_default_environment

        return cls.__default_environment

    @classmethod
    def set_external_default(cls, env):
        assert isinstance(env, cls)
        cls.__external_default_environment = env

    def __init__(self, constants={}, mutinds={}, variables={}):
        self.__constants = constants
        self.__mutinds = mutinds
        self.__variables = variables

        self.inherited_environment = None

    def get_builtins(self):
        builtins = Environment()

        for const in self.__constants.values():
            if const.is_builtin:
                builtins.add_constant(const)

        for mutind in self.__mutinds.values():
            if mutind.is_builtin:
                builtins.add_mutind(mutind)

        return builtins

    def __iadd__(self, env):
        assert isinstance(env, Environment)
        self.__constants.update(env.constants())
        self.__mutinds.update(env.mutinds())

        return self

    def declare_variable(self, ident, typ):
        if ident in self.variables:
            raise KeyError("variable %s already exists!" % ident)

        from .declaration import Constant
        self.__variables[ident] = Constant(ident, typ)

    def declare_constant(self, ident, typ, body, is_builtin=False):
        if ident in self.__constants:
            raise KeyError("constant %s already exists!" % ident)

        from .declaration import Constant
        self.__constants[ident] = Constant(ident, typ, body, is_builtin)

    # the three functions `add_......` are mainly used when directly copy something
    # from one environment to another. it DOES NOT check whether the identifier is
    # already exist. so please be careful when using them

    def add_variable(self, var: 'Constant'):
        """
        be aware of knowing what you are doing!
        """
        self.__variables[var.name] = var

    def add_constant(self, const):
        """
        be aware of knowing what you are doing!
        """
        self.__constants[const.name] = const

    def add_mutind(self, mutind):
        """
        be aware of knowing what you are doing!
        """
        self.__mutinds[mutind.name] = mutind

    def constants(self):
        return self.__constants

    def variables(self):
        return self.__variables

    def mutinds(self):
        return self.__mutinds

    def constant(self, name):
        if name in self.__constants:
            return self.__constants[name]
        elif self.inherited_environment is not None:
            return self.inherited_environment.constant(name)
        else:
            raise KeyError("constant %s not found in the environment" % name)

    def variable(self, name):
        if name in self.__variables:
            return self.__variables[name]
        elif self.inherited_environment is not None:
            return self.inherited_environment.variable(name)
        else:
            raise KeyError("variable %s not found in the environment" % name)

    def mutind(self, name):
        if name in self.__mutinds:
            return self.__mutinds[name]
        elif self.inherited_environment is not None:
            return self.inherited_environment.mutind(name)
        else:
            raise KeyError("mut-inductive %s not found in the environment" % name)

    def __repr__(self):
        return "<holboost environment with %d constants, %d mut-inductives and %d variables%s>" % (
                len(self.__constants),
                len(self.__mutinds),
                len(self.__variables),
                "" if self.inherited_environment is None else ", inherited"
                )

    def __str__(self):
        rel = "<holboost environment with %d constants, %d mut-inductives and %d variables>" % (
                len(self.__constants),
                len(self.__mutinds),
                len(self.__variables)
                )

        if self.inherited_environment is not None:
            rel += "\n  |- " + str(self.inherited_environment)

        return rel
