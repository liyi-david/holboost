import abc
import enum

class TypingUnclosedError(Exception):
    pass

class Term(abc.ABC):

    # if a term is created by a notation, then the way it is rendered depends on the notation
    # notations have no semantics
    notation: 'Notation' = None

    @abc.abstractmethod
    def type(self, environment, context=[]) -> 'Term':
        pass

    @abc.abstractmethod
    def render(self, environment=None, context=[], debug=False) -> 'str':
        pass

    @abc.abstractmethod
    def __eq__(self, value):
        pass

    @abc.abstractmethod
    def subterms(self):
        """ this function obtains all subterms in this term """
        pass

    @abc.abstractmethod
    def subterms_subst(self, subterms):
        """ this function replace subterms by a given list """
        pass

    def __str__(self) -> 'str':
        return self.render()

    def istype(self, environment=None) -> 'bool':
        if isinstance(self.type(environment), Sort) and self.type(environment).sort is SortEnum.type:
            return True

        return False

    def rels_subst(self, ctx_values, depth=0):
        """
        it is important to figure out how this function works precisely.

        1. it replace all the free variables in `self` by the values given in ctx_values
        2. depth is used to denote how many bounded variables, i.e. context terms we have
        """
        subterms = self.subterms()
        for i in range(len(subterms)):
            if isinstance(self, ContextTerm) and i == len(subterms) - 1:
                # if the subterm is a body of LetIn, Lambda or Prod
                subterms[i] = subterms[i].rels_subst(ctx_values, depth + 1)
            else:
                subterms[i] = subterms[i].rels_subst(ctx_values, depth)

        return self.subterms_subst(subterms)


class SortEnum(enum.Enum):
    prop = 'Prop'
    set  = 'Set'
    type = 'Type'


class Sort(Term):
    def __init__(self, sort: 'SortEnum'):
        self.sort = sort

    def type(self, environment, context=[]) -> 'Term':
        return Sort(SortEnum.type)

    def render(self, environment=None, context=[], debug=False) -> 'str':
        return self.sort.value

    def __eq__(self, value):
        return isinstance(value, Sort) and value.sort == self.sort

    def subterms(self):
        return []

    def subterms_subst(self, subterms):
        """ sort contains no sub-term and hence cannot be substituted """
        return self


TYPE = Sort(SortEnum.type)
PROP = Sort(SortEnum.prop)
SET  = Sort(SortEnum.set)


class Cast(Term):

    def __init__(self, body: 'Term', cast_kind: 'int', guaranteed_type: 'Term'):
        # cast_kind is a hash
        # 0 - VMcast, 1 - NATIVEcast, 2 - DEFAULTcast, 3 - REVERTcast
        # IMPORTANT! it must be consistent with the coq serializer
        self.body = body
        self.cast_kind = cast_kind
        self.guaranteed_type = guaranteed_type

    def type(self, environment, context=[]) -> 'Term':
        return self.guaranteed_type

    def render(self, environment=None, context=[], debug=False) -> 'str':
        # FIXME the cast_kind?
        return "%s : %s" % (
                self.body.render(environment, context, debug),
                self.guaranteed_type.render(environment, context, debug)
                )

    def __eq__(self, value):
        return isinstance(value, Cast) and \
                self.body == value.body and \
                self.guaranteed_type == value.guaranteed_type

    def subterms(self):
        return [self.body, self.guaranteed_type]

    def subterms_subst(self, subterms):
        return Cast(subterms[0], self.cast_kind, subterms[1])


class Const(Term):
    def __init__(self, name: 'str'):
        self.name = name

    def type(self, environment, context=[]) -> 'Term':
        return environment.constants[self.name].type

    def render(self, environment=None, context=[], debug=False) -> 'str':
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

    def subterms_subst(self, subterms):
        return self

class Case(Term):
    # TODO not finished yet!!
    def __init__(self):
        pass

    def type(self, environment, context=[]) -> 'Term':
        raise Exception('unimplemented')

    def render(self, environment=None, context=[], debug=False) -> 'str':
        return 'CASE'

    def __eq__(self, value):
        return False

    def subterms(self):
        return []

    def subterms_subst(self, subterms):
        return self


class Evar(Term):
    # TODO not finished yet!!
    def __init__(self):
        pass

    def type(self, environment, context=[]) -> 'Term':
        raise Exception('unimplemented')

    def render(self, environment=None, context=[], debug=False) -> 'str':
        return 'EVAR'

    def __eq__(self, value):
        return False

    def subterms(self):
        return []

    def subterms_subst(self, subterms):
        return self


class Var(Const):

    def type(self, environment) -> 'Term':
        return environment.variables[self.name].type

    def render(self, environment=None, context=[], debug=False) -> 'str':
        found = False
        try:
            if self.name in environment.variables: found = True
        except:
            # TODO add log to the top!
            pass

        if not debug and found:
            return self.name.split('.')[-1]
        else:
            return Const.render(self, debug)


class Rel(Term):
    def __init__(self, index: int):
        # all indexes in holboost must start from zero !!!!!!
        self.index = index

    def type(self, environment, context=[]) -> 'Term':
        binding = self.get_binding(context)
        if binding is None:
            raise TypingUnclosedError()

        return binding.arg_type

    def render(self, environment=None, context=[], debug=False) -> 'str':
        binding = self.get_binding(context)
        if binding is None or debug:
            return "_REL_%d_" % self.index
        else:
            return binding.arg_name

    def get_binding(self, context):
        # if self.index = 0, we get the last bounded variable, e.g. context[-1]
        if len(context) <= self.index:
            return None

        return context[ -1 * (self.index + 1) ]

    def __eq__(self, value):
        return isinstance(value, Rel) and value.index == self.index

    def subterms(self):
        return []

    def subterms_subst(self, subterms):
        return self

    def rels_subst(self, ctx_rels, depth=0):
        # the rel variable is still bounded
        if self.index < depth:
            return self

        # for example, given a term with type
        # forall n, m: nat, n >= m, if we wanna apply it to a single number n = 0, i.e.
        # we wanna have forall m: nat, 0 >= m
        # in this case, we we iterate to "n >= m", we have depth = 1, and n is Rel(1), the correct
        # index is -1 * ((1 - depth) + 1)
        return ctx_rels[ -1 * ((self.index - depth) + 1) ]


class Apply(Term):
    def __init__(self, func: 'Term', *args: 'Term'):
        self.func = func
        self.args = args

    def type(self, environment, context=[]) -> 'Term':
        func_type = self.func.type(environment)

        # if the type of func is A -> B -> C and there are two arguments, then the type of the whole term
        # should be C
        # if there is only one argument, it should be B -> C
        # ..

        typ = self.func.type(environment, context)
        for i in range(len(self.args)): typ = typ.body

        # if there are no rel variables in `typ`, that's it
        # otherwise it is a dependent type
        # in this case we will replace the rels in the type term with the arguments applied to this function

        return typ.rels_subst(self.args)


    def render(self, environment=None, context=[], debug=False) -> 'str':
        return '({0} {1})'.format(
                self.func.render(environment, context, debug),
                ' '.join(map(lambda t: t.render(environment, context, debug), self.args))
                )

    def __eq__(self, value):
        return isinstance(value, Apply) and \
                value.func == self.func and \
                value.args == self.args

    def subterms(self):
        return [self.func] + list(self.args)

    def subterms_subst(self, subterms):
        return Apply(*subterms)


class ContextTerm(Term):
    def __init__(self, arg_name: 'str', arg_type: 'Term', body: 'Term'):
        self.arg_name = arg_name
        self.arg_type = arg_type
        self.body = body


class Prod(ContextTerm):
    def type(self, environment, context=[]) -> 'Term':
        # FIXME have a double check?
        return TYPE

    def render(self, environment=None, context=[], debug=False) -> 'str':
        # TODO
        # if self.id exists but not used in the sub term, we should also print arrow form
        if self.arg_name is None:
            # arrow form
            return "{0} -> {1}".format(
                    self.arg_type.render(environment, context, debug),
                    self.body.render(environment, context + [self], debug)
                    )
        else:
            # forall form
            # combine multiple foralls if possible
            return "forall {0}: {1}, {2}".format(
                    self.arg_name,
                    self.arg_type.render(environment, context, debug),
                    self.body.render(environment, context + [self], debug)
                    )

    def __eq__(self, value):
        return isinstance(value, Prod) and \
                value.arg_name == self.arg_name and \
                value.arg_type == self.arg_type and \
                value.body == self.body

    def subterms(self):
        return [self.arg_type, self.body]

    def subterms_subst(self, subterms):
        return Prod(self.arg_name, *subterms)


class LetIn(ContextTerm):
    def __init__(self, arg_name: 'str', arg_type: 'Term', arg_body: 'Term', body: 'Term'):
        ContextTerm.__init__(self, arg_name, arg_type, body)
        self.arg_body = arg_body

    def type(self, environment, context=[]) -> 'Term':
        return self.body.type(environment, context + [self])

    def render(self, environment=None, context=[], debug=False) -> 'str':
        return "let {0} : {1} := {2} in {3}".format(
                self.arg_name,
                self.arg_type.render(environment, context, debug),
                self.arg_body.render(environment, context, debug),
                self.body.render(environment, context + [self], debug)
                )

    def __eq__(self, value):
        return isinstance(value, Prod) and \
                value.arg_name == self.arg_name and \
                value.arg_type == self.arg_type and \
                value.arg_body == self.arg_body and \
                value.body == self.body

    def subterms(self):
        return [self.arg_type, self.arg_body, self.body]

    def subterms_subst(self, subterms):
        return Prod(self.arg_name, *subterms)


class Lambda(ContextTerm):

    def type(self, environment, context=[]) -> 'Term':
        return Prod(None, self.arg_type, self.body.type(environment, context + [self]))

    def render(self, environment=None, context=[], debug=False) -> 'str':
        return "fun ({0}: {1}) => {2}".format(
                self.arg_name,
                self.arg_type.render(environment, context, debug),
                self.body.render(environment, context + [self], debug)
                )

    def __eq__(self, value):
        return isinstance(value, Prod) and \
                value.arg_name == self.arg_name and \
                value.arg_type == self.arg_type and \
                value.body == self.body

    def subterms(self):
        return [self.arg_type, self.body]

    def subterms_subst(self, subterms):
        return Prod(self.arg_name, *subterms)


class Construct(Term):
    def __init__(self, mutind: 'str', ind_index: int, constructor_index: int):
        self.mutind_name = mutind
        self.ind_index = ind_index
        self.constructor_index = constructor_index

    def type(self, environment, context=[]) -> 'Term':
        ind = environment.mutinds[self.mutind_name].inds[self.ind_index]
        ind_type = ind.type(environment)
        raw_type = ind.constructors[self.constructor_index].type(environment)
        return raw_type.rels_subst([Ind(self.mutind_name, self.ind_index)])

    def render(self, environment=None, context=[], debug=False) -> 'str':
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

    def subterms_subst(self, subterms):
        return self


class Ind(Term):
    def __init__(self, mutind: 'str', ind_index: int):
        self.mutind_name = mutind
        self.ind_index = ind_index

    def type(self, environment, context=[]) -> 'Term':
        return environment.mutinds[self.mutind_name].inds[self.ind_index].type(environment)

    def render(self, environment=None, context=[], debug=False) -> 'str':
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

    def subterms_subst(self, subterms):
        return self
