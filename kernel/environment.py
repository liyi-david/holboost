from abc import ABCMeta, abstractmethod

"""
NOTES
===

make sure to read these notes before starting using function interfaces provided in this file.

1. the query functions, e.g. constants/mutinds/constant/ind/.... are time-consuming. when you try to write
   a performance-critical function (tactic, rewriting, etc.) please try to AVOID using them

2. TBD

"""

# this is only used as a constant
lambda_type = type(lambda f: f)

def prefix_of(ident):
    return ".".join(ident.split(".")[:-1])



class EnvironmentOverflow(Exception):
    pass

class Environment(metaclass=ABCMeta):

    __default_environment = None
    __external_default_environment = None

    def __init__(self):
        self.inherited_environment = None

    # when an environment is inherited, it should not be changed!
    _blocked = False

    def block(self): self._blocked = True
    def unblock(self): self._blocked = False

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

    # ============================ abstract interfaces ========================

    @abstractmethod
    def constants(self):
        pass

    @abstractmethod
    def variables(self):
        pass

    @abstractmethod
    def mutinds(self):
        pass

    @abstractmethod
    def inds(self):
        pass

    @abstractmethod
    def constructors(self):
        pass

    def rel(self, index):
        """
        index starts from zero !
        """
        if self.inherited_environment is not None:
            return self.inherited_environment.rel(index)
        else:
            raise IndexError("cannot find relational variable!")

    @abstractmethod
    def lookup_by_binding(self, binding):
        pass

    # =========================== common interfaces ===========================

    def constant(self, _filter):
        assert isinstance(_filter, (str, lambda_type)), "string or lambda functions are supposed when looking up declarations"

        if isinstance(_filter, str):
            name = _filter
            _filter = lambda s: s == name

        return list(filter(
            lambda item: _filter(item.name), self.constants().values()
            ))

    def variable(self, _filter):
        assert isinstance(_filter, (str, lambda_type)), "string or lambda functions are supposed when looking up declarations"

        if isinstance(_filter, str):
            name = _filter
            _filter = lambda s: s == name

        return list(filter(
            lambda item: _filter(item.name), self.variables().values()
            ))

    def mutind(self, _filter):
        assert isinstance(_filter, (str, lambda_type)), "string or lambda functions are supposed when looking up declarations"

        if isinstance(_filter, str):
            name = _filter
            _filter = lambda s: s == name

        return list(filter(
            lambda item: _filter(item.name), self.mutinds().values()
            ))

    def ind(self, _filter):
        assert isinstance(_filter, (str, lambda_type)), "string or lambda functions are supposed when looking up declarations"

        if isinstance(_filter, str):
            name = _filter
            _filter = lambda s: s == name

        return list(filter(
            lambda ind: _filter(ind.name),
            self.inds().values()
            ))

    def constructor(self, _filter):
        assert isinstance(_filter, (str, lambda_type)), "string or lambda functions are supposed when looking up declarations"

        if isinstance(_filter, str):
            name = _filter
            _filter = lambda s: s == name

        return list(filter(
            lambda c: _filter(c.name),
            self.constructors().values()
            ))

    # =============================== syntax sugars ===========================

    def __getitem__(self, ident):
        filt = lambda n: n == ident or n.endswith('.' + ident)
        results = self.variable(filt) + self.constant(filt) + self.constructor(filt) + self.ind(filt) + self.mutind(filt)

        if len(results) > 0:
            return results[0]
        else:
            raise KeyError("identifier %s is not found." % ident)

    def __str__(self):
        rel = repr(self)

        if self.inherited_environment is not None:
            return str(self.inherited_environment) + u"\n|- " + rel
        else:
            return rel



class NamedEnvironment(Environment):

    def __init__(self, constants={}, mutinds={}, variables={}):
        Environment.__init__(self)

        self.__constants = constants
        self.__mutinds = mutinds
        self.__variables = variables

        # prefixes contain only the prefixes of mutinds and constants
        # they are basically used to figure out whether a variable is
        # cached or not
        self.__prefixes = set()

    def get_builtins(self):
        """
        only named environments carries builtins
        """
        builtins = NamedEnvironment()

        for const in self.__constants.values():
            if const.is_builtin:
                builtins.add_constant(const)

        for mutind in self.__mutinds.values():
            if mutind.is_builtin:
                builtins.add_mutind(mutind)

        return builtins

    def __iadd__(self, env):
        """
        the '+=' operator only changes mut-inductives and definition
        """
        assert isinstance(env, NamedEnvironment)
        for c in env.constants().values():
            self.add_constant(c)

        for m in env.mutinds().values():
            self.add_mutind(m)

        return self

    def declare_variable(self, ident, typ):
        if ident in self.__variables:
            raise KeyError("variable %s already exists in the local environment!" % ident)

        from .declaration import Variable
        self.__variables[ident] = Variable(ident, typ)

    def declare_variables(self, idents, typ):
        for ident in idents:
            self.declare_variable(ident, typ)

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

    def add_constant(self, const: 'Constant'):
        """
        be aware of knowing what you are doing!
        """
        self.__constants[const.name] = const
        # self.__prefixes.add(prefix_of(const.name))

    def add_mutind(self, mutind: 'MutInductive'):
        """
        be aware of knowing what you are doing!
        """
        self.__mutinds[mutind.name] = mutind
        # self.__prefixes.add(prefix_of(mutind.name))

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

    def lookup_by_binding(self, binding):
        if self.inherited_environment is None:
            raise EnvironmentOverflow
        else:
            return self.inherited_environment.lookup_by_binding(binding)

    def __repr__(self):
        return "<holboost named environment with %d constants, %d mut-inductives and %d variables%s>" % (
                len(self.__constants),
                len(self.__mutinds),
                len(self.__variables),
                "" if self.inherited_environment is None else ", inherited"
                )


class ContextEnvironment(Environment):

    def __init__(self, binding, env):
        Environment.__init__(self)

        self.binding = binding
        self.inherited_environment = env

    def constants(self):
        if self.inherited_environment is not None:
            return self.inherited_environment.constants()
        else:
            return {}

    def variables(self):
        if self.inherited_environment is not None:
            return self.inherited_environment.variables()
        else:
            return {}

    def mutinds(self):
        if self.inherited_environment is not None:
            return self.inherited_environment.mutinds()
        else:
            return {}

    def inds(self):
        if self.inherited_environment is not None:
            return self.inherited_environment.inds()
        else:
            return {}

    def constructors(self):
        if self.inherited_environment is not None:
            return self.inherited_environment.constructors()
        else:
            return {}

    def rel(self, index):
        if index == 0:
            return self.binding
        else:
            if self.inherited_environment is not None:
                return self.inherited_environment.rel(index - 1)
            else:
                raise KeyError("unbounded variable index %d" % index)

    def length(self):
        l = 1
        pt = self
        while pt.inherited_environment is not None and isinstance(pt.inherited_environment, ContextEnvironment):
            pt = pt.inherited_environment
            l += 1

        return l

    def lookup_by_binding(self, binding):
        if self.binding == binding:
            return self, 0
        else:
            if self.inherited_environment is None:
                raise EnvironmentOverflow

            ctx, index = self.inherited_environment.lookup_by_binding(binding)
            return ctx, index + 1

    def __repr__(self):
        return "<holboost context: (%s)>" % self.binding.render(self.inherited_environment)
