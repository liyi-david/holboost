import abc
import enum

class Term(abc.ABC):

    # each term belongs to a parent
    parent : 'Term' = None

    # if a term is created by a notation, then the way it is rendered depends on the notation
    # notations have no semantics
    notation: 'Notation' = None

    def setParent(self, parent: 'Term') -> 'NoneType':
        self.parent = parent

    @abc.abstractmethod
    def type(self) -> 'Term':
        pass

    @abc.abstractmethod
    def render(self, environment=None, debug=False) -> 'str':
        pass

    @abc.abstractmethod
    def __eq__(self, value):
        pass

    @abc.abstractmethod
    def subterms(self):
        pass

    def __str__(self) -> 'str':
        return self.render()

    def istype(self) -> 'bool':
        if isinstance(self.type(), Sort) and self.type().sort is SortEnum.type:
            return True

        return False


class SortEnum(enum.Enum):
    prop = 'Prop'
    set  = 'Set'
    type = 'Type'


class Sort(Term):
    def __init__(self, sort: 'SortEnum'):
        self.sort = sort

    def type(self) -> 'Term':
        return Sort(SortEnum.type)

    def render(self, environment=None, debug=False) -> 'str':
        return self.sort.value

    def __eq__(self, value):
        return isinstance(value, Sort) and value.sort == self.sort

    def subterms(self):
        return []


TYPE = Sort(SortEnum.type)
PROP = Sort(SortEnum.prop)
SET  = Sort(SortEnum.set)


class Const(Term):
    def __init__(self, name: 'str'):
        self.name = name

    def type(self) -> 'Term':
        raise Exception('unimplemented')

    def render(self, environment=None, debug=False) -> 'str':
        found = False
        try:
            if self.name in environment.constants: found = True
        except:
            # TODO add log to the top!
            pass

        if not debug and found:
            # for Coq.Init.Peano.gt we only return `gt`
            # if debug mode is not activated
            return self.name.split('.')[-1]
        else:
            return self.name

    def __eq__(self, value):
        return isinstance(value, Const) and self.name == value.name

    def subterms(self):
        return []

class Case(Term):
    # TODO not finished yet!!
    def __init__(self):
        pass

    def type(self) -> 'Term':
        raise Exception('unimplemented')

    def render(self, environment=None, debug=False) -> 'str':
        return 'CASE'

    def __eq__(self, value):
        return False

    def subterms(self):
        return []


class Var(Const):
    def render(self, environment=None, debug=False) -> 'str':
        found = False
        try:
            if self.name in environment.context_variables: found = True
        except:
            # TODO add log to the top!
            pass

        if not debug and found:
            return self.name.split('.')[-1]
        else:
            return "[VAR: %s]" % Const.render(self, debug)


class Rel(Term):
    def __init__(self, index: int):
        # all indexes in holboost must start from zero !!!!!!
        self.index = index

    def type(self) -> 'Term':
        if self.ref is None:
            pass
        else:
            return self.ref.arg_type

    def render(self, environment=None, debug=False) -> 'str':
        pt = self
        curr_rel_index = -1
        while pt.parent is not None and isinstance(pt.parent, Term):
            pt = pt.parent
            if isinstance(pt, (LetIn, Lambda, Prod)):
                curr_rel_index += 1
                if curr_rel_index == self.index:
                    return pt.arg_name

        return "_REL_%d_" % self.index

    def __eq__(self, value):
        return isinstance(value, Rel) and value.index == self.index

    def subterms(self):
        return []


class Apply(Term):
    def __init__(self, func: 'Term', *args: 'Term'):
        self.func = func
        self.func.setParent(self)
        self.args = args
        for arg in args:
            arg.setParent(self)

    def type(self) -> 'Term':
        raise Exception('unimplemented')

    def render(self, environment=None, debug=False) -> 'str':
        return '({0} {1})'.format(
                self.func.render(environment, debug),
                ' '.join(map(lambda t: t.render(environment, debug), self.args))
                )

    def __eq__(self, value):
        return isinstance(value, Apply) and \
                value.func == self.func and \
                value.args == self.args

    def subterms(self):
        return [self.func] + list(self.args)


class Prod(Term):
    def __init__(self, arg_name: 'str', arg_type: 'Term', body: 'Term'):
        self.arg_name = arg_name
        self.arg_type = arg_type
        self.arg_type.setParent(self)
        self.body = body
        self.body.setParent(self)

    def type(self) -> 'Term':
        raise Exception('unimplemented')

    def render(self, environment=None, debug=False) -> 'str':
        # TODO
        # if self.id exists but not used in the sub term, we should also print arrow form
        if self.arg_name is None:
            # arrow form
            return "{0} -> {1}".format(
                    self.arg_type.render(environment, debug),
                    self.body.render(environment, debug)
                    )
        else:
            # forall form
            # combine multiple foralls if possible
            return "forall {0}: {1}, {2}".format(
                    self.arg_name,
                    self.arg_type.render(environment, debug),
                    self.body.render(environment, debug)
                    )

    def __eq__(self, value):
        return isinstance(value, Prod) and \
                value.arg_name == self.arg_name and \
                value.arg_type == self.arg_type and \
                value.body == self.body

    def subterms(self):
        return [self.arg_type, self.body]


class LetIn(Term):
    def __init__(self, arg_name: 'str', arg_type: 'Term', arg_body: 'Term', body: 'Term'):
        self.arg_name = arg_name
        self.arg_type = arg_type
        self.arg_type.setParent(self)
        self.arg_body = arg_body
        self.arg_body.setParent(self)
        self.body = body
        self.body.setParent(self)

    def type(self) -> 'Term':
        raise Exception('unimplemented')

    def render(self, environment=None, debug=False) -> 'str':
        return "let {0} : {1} := {2} in {3}".format(
                self.arg_name,
                self.arg_type.render(environment, debug),
                self.arg_body.render(environment, debug),
                self.body.render(environment, debug)
                )

    def __eq__(self, value):
        return isinstance(value, Prod) and \
                value.arg_name == self.arg_name and \
                value.arg_type == self.arg_type and \
                value.arg_body == self.arg_body and \
                value.body == self.body

    def subterms(self):
        return [self.arg_type, self.arg_body, self.body]


class Lambda(Term):
    def __init__(self, argname: 'str', argtype: 'Term', body: 'Term'):
        self.arg_name = argname
        self.arg_type = argtype
        self.arg_type.setParent(self)
        self.body = body
        self.body.setParent(self)

    def type(self) -> 'Term':
        raise Exception('unimplemented')

    def render(self, environment=None, debug=False) -> 'str':
        return "fun ({0}: {1}) => {2}".format(
                self.arg_name,
                self.arg_type.render(environment, debug),
                self.body.render(environment, debug)
                )

    def __eq__(self, value):
        return isinstance(value, Prod) and \
                value.arg_name == self.arg_name and \
                value.arg_type == self.arg_type and \
                value.body == self.body

    def subterms(self):
        return [self.arg_type, self.body]


class Construct(Term):
    def __init__(self, mutind: 'str', ind_index: int, constructor_index: int):
        self.mutind_name = mutind
        self.ind_index = ind_index
        self.constructor_index = constructor_index

    def type(self) -> 'Term':
        raise Exception('unimplemented')

    def render(self, environment=None, debug=False) -> 'str':
        found = False
        construct_name = None

        try:
            if self.mutind_name in environment.mutinds:
                construct_name = environment.mutinds[self.mutind_name].inds[self.ind_index].constructors[self.constructor_index].name
                found = True
        except:
            # TODO log
            pass

        if not debug and found:
            return construct_name
        else:
            return '_%s_%d_%d_' % (self.mutind_name, self.ind_index, self.constructor_index)

    def __eq__(self, value):
        return isinstance(value, Construct) and \
                value.mutind_name == self.mutind_name and \
                value.ind_index == self.ind_index and \
                value.constructor_index == self.constructor_index

    def subterms(self):
        return []


class Ind(Term):
    def __init__(self, mutind: 'str', ind_index: int):
        self.mutind_name = mutind
        self.ind_index = ind_index

    def type(self) -> 'Term':
        raise Exception('unimplemented')

    def render(self, environment=None, debug=False) -> 'str':
        found = False
        ind_name = None

        try:
            if self.mutind_name in environment.mutinds:
                ind_name = environment.mutinds[self.mutind_name].inds[self.ind_index].name
                found = True
        except:
            # TODO log
            pass

        if not debug and found:
            return ind_name
        else:
            return '_%s_%d_' % (self.mutind_name, self.ind_index)

    def __eq__(self, value):
        return isinstance(value, Ind) and \
                value.mutind_name == self.mutind_name and \
                value.ind_index == self.ind_index

    def subterms(self):
        return []
