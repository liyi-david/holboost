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
    def export(self) -> 'str':
        pass

    def __str__(self) -> 'str':
        return self.export()

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

    def export(self) -> 'str':
        return self.sort.value

TYPE = Sort(SortEnum.type)
PROP = Sort(SortEnum.prop)
SET  = Sort(SortEnum.set)


class Const(Term):
    def __init__(self, name: 'str'):
        self.name = name

    def type(self) -> 'Term':
        raise Exception('unimplemented')

    def export(self) -> 'str':
        return self.name


class Var(Const):
    pass


class Rel(Term):
    def __init__(self, index: int):
        self.index = index
        self.ref = None

    def type(self) -> 'Term':
        if self.ref is None:
            pass
        else:
            return self.ref.arg_type

    def export(self) -> 'str':
        if self.ref is None:
            return "_REL_%d_" % self.index
        else:
            return self.ref.arg_name


class Apply(Term):
    def __init__(self, func: 'Term', *args: 'Term'):
        self.func = func
        self.args = args

    def type(self) -> 'Term':
        raise Exception('unimplemented')

    def export(self) -> 'str':
        return '({0} {1})'.format(
                self.func.export(),
                ' '.join(map(lambda t: t.export(), self.args))
                )


class Prod(Term):
    def __init__(self, id: 'str', type: 'Term', body: 'Term'):
        self.id = id
        self.type = type
        self.type.setParent(self)
        self.body = body
        self.body.setParent(self)

    def type(self) -> 'Term':
        raise Exception('unimplemented')

    def export(self) -> 'str':
        # TODO
        # if self.id exists but not used in the sub term, we should also print arrow form
        if self.id is None:
            # arrow form
            return "{0} -> {1}".format(self.type.export(), self.body.export())
        else:
            # forall form
            # combine multiple foralls if possible
            return "forall {0}: {1}, {2}".format(self.id, self.type.export(), self.body.export())


class LetIn(Term):
    def __init__(self, id: 'str', type: 'Term', body: 'Term'):
        assert id is not None
        self.id = id
        self.type = type
        self.type.setParent(self)
        self.body = body
        self.body.setParent(self)

    def type(self) -> 'Term':
        raise Exception('unimplemented')

    def export(self) -> 'str':
        return "let {0} := {1} in {2}".format(self.id, self.type.export(), self.body.export())


class Lambda(Term):
    def __init__(self, argname: 'str', argtype: 'Term', body: 'Term'):
        assert id is not None
        self.arg_name = argname
        self.arg_type = argtype
        self.arg_type.setParent(self)
        self.body = body
        self.body.setParent(self)

    def type(self) -> 'Term':
        raise Exception('unimplemented')

    def export(self) -> 'str':
        return "fun ({0}: {1}) => {2}".format(self.arg_name, self.arg_type.export(), self.body.export())


class Construct(Term):
    def __init__(self, mutind: 'str', ind_index: int, constructor_index: int):
        self.mutind_name = mutind
        self.mutind_ref = None
        self.ind_index = ind_index
        self.constructor_index = constructor_index

    def type(self) -> 'Term':
        raise Exception('unimplemented')

    def export(self) -> 'str':
        if self.mutind_ref is None:
            return '_%s_%d_%d_' % (self.mutind_name, self.ind_index, self.constructor_index)
        else:
            pass


class Ind(Term):
    def __init__(self, mutind: 'str', ind_index: int):
        self.mutind_name = mutind
        self.mutind_ref = None
        self.ind_index = ind_index

    def type(self) -> 'Term':
        raise Exception('unimplemented')

    def export(self) -> 'str':
        if self.mutind_ref is None:
            return '_%s_%d_' % (self.mutind_name, self.ind_index)
        else:
            pass
