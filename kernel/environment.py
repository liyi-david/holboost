
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
        if ident in self.__variables:
            raise KeyError("variable %s already exists in the local environment!" % ident)

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
        result = self.__constants.copy()
        if self.inherited_environment is not None:
            result.update(self.inherited_environment.constants())

        return result

    def variables(self):
        result = self.__variables.copy()
        if self.inherited_environment is not None:
            result.update(self.inherited_environment.variables())

        return result

    def mutinds(self):
        result = self.__mutinds.copy()
        if self.inherited_environment is not None:
            result.update(self.inherited_environment.mutinds())

        return result

    def inds(self):
        inds = {}
        for mutind in self.mutinds().values():
            inds.update({ ind.name: ind for ind in mutind.inds })

        return inds

    def constructors(self):
        constructors = {}
        for ind in self.inds().values():
            constructors.update({ c.name: c for c in ind.constructors })

        return constructors


    def constant(self, _filter):
        assert isinstance(_filter, (str, type(lambda f: f))), "string or lambda functions are supposed when looking up declarations"

        if isinstance(_filter, str):
            name = _filter
            _filter = lambda s: s == name

        return list(filter(
            lambda item: _filter(item.name), self.constants().values()
            ))

    def variable(self, _filter):
        assert isinstance(_filter, (str, type(lambda f: f))), "string or lambda functions are supposed when looking up declarations"

        if isinstance(_filter, str):
            name = _filter
            _filter = lambda s: s == name

        return list(filter(
            lambda item: _filter(item.name), self.variables().values()
            ))

    def mutind(self, _filter):
        assert isinstance(_filter, (str, type(lambda f: f))), "string or lambda functions are supposed when looking up declarations"

        if isinstance(_filter, str):
            name = _filter
            _filter = lambda s: s == name

        return list(filter(
            lambda item: _filter(item.name), self.mutinds().values()
            ))

    def ind(self, _filter):
        assert isinstance(_filter, (str, type(lambda f: f))), "string or lambda functions are supposed when looking up declarations"

        if isinstance(_filter, str):
            name = _filter
            _filter = lambda s: s == name

        return list(filter(
            lambda ind: _filter(ind.name),
            self.inds().values()
            ))


    def constructor(self, _filter):
        assert isinstance(_filter, (str, type(lambda f: f))), "string or lambda functions are supposed when looking up declarations"

        if isinstance(_filter, str):
            name = _filter
            _filter = lambda s: s == name

        return list(filter(
            lambda c: _filter(c.name),
            self.constructors().values()
            ))



    def __getitem__(self, ident):
        filt = lambda n: n.split(".")[-1] == ident
        results = self.variable(filt) + self.constant(filt) + self.constructor(filt) + self.ind(filt) + self.mutind(filt)

        if len(results) > 0:
            return results[0]
        else:
            raise KeyError("identifier %s is not found." % ident)

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
