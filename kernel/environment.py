
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

    def constant(self, _filter):
        assert isinstance(_filter, (str, type(lambda f: f))), "string or lambda functions are supposed when looking up declarations"

        if isinstance(_filter, str):
            name = _filter
            _filter = lambda s: s == name

        satisfied = list(map(
            lambda name: self.__constants[name],
            filter(_filter, self.__constants.keys())
            ))

        if self.inherited_environment is not None:
            satisfied += self.inherited_environment.constant(_filter)

        return satisfied

    def variable(self, _filter):
        assert isinstance(_filter, (str, type(lambda f: f))), "string or lambda functions are supposed when looking up declarations"

        if isinstance(_filter, str):
            name = _filter
            _filter = lambda s: s == name

        satisfied = list(map(
            lambda name: self.__variables[name],
            filter(_filter, self.__variables.keys())
            ))

        if self.inherited_environment is not None:
            satisfied += self.inherited_environment.variable(_filter)

        return satisfied

    def mutind(self, _filter):
        assert isinstance(_filter, (str, type(lambda f: f))), "string or lambda functions are supposed when looking up declarations"

        if isinstance(_filter, str):
            name = _filter
            _filter = lambda s: s == name

        satisfied = list(map(
            lambda name: self.__mutinds[name],
            filter(_filter, self.__mutinds.keys())
            ))

        if self.inherited_environment is not None:
            satisfied += self.inherited_environment.mutind(_filter)

        return satisfied

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
