import abc
import enum

from .task import Task
from .environment import Environment, ContextEnvironment
from .universe import Universe, UniverseInstance, NativeLevels

from lib.common import all_are_same_instances, one_of_them_is


class TypingUnclosedError(Exception):
    pass

class Binding:
    def __init__(self, name, value, type):
        self.name = name
        self.value = value
        self.type = type

    @classmethod
    def from_json(cls, json_item):
        return cls(
                None if 'name' not in json_item else json_item['name'],
                None if 'value' not in json_item else Term.from_json(json_item['value']),
                None if 'type' not in json_item else Term.from_json(json_item['type'])
                )

    @classmethod
    def from_term(cls, term):
        assert isinstance(term, ContextTerm), "grab context binding from only context terms!"
        return cls(
            term.arg_name,
            term.arg_body if isinstance(term, LetIn) else None,
            term.arg_type
        )

    def render(self, environment=None, debug=False):
        return "%s%s%s" % (
                "_" if self.name is None else self.name,
                "" if self.type is None else " : " + self.type.render(environment, debug),
                "" if self.value is None else " := " + self.value.render(environment, debug)
                )

    def __repr__(self):
        return self.render()



class Term(abc.ABC):

    # if a term is created by a notation, then the way it is rendered depends on the notation
    # notations have no semantics
    notation: 'Notation' = None

    def __init__(self):
        self.comment = None

    @classmethod
    def from_json(cls, json_item):
        from interaction.formats.json import JsonFormat
        return JsonFormat.import_term(json_item)

    def to_json(self):
        from interaction.formats.json import JsonFormat
        return JsonFormat.export_term(self)

    @abc.abstractmethod
    def type(self, environment=None) -> 'Term':
        pass

    @abc.abstractmethod
    def check(self, environment=None) -> 'Term * list(LevelConstraint)':
        """
        when `type` is called, we always assume that the term itself is type-safe. however, sometimes
        we manually construct a term (not imported from Coq or other tools), in this case we need to
        check the type-safety of this term.

        the function returns a tuple which includes:

            - the type of this term, should be exactly the same with the result of `type`
            - a list of level constraints that describe the side effect

        """
        pass

    def side_effects(self, environment):
        _, s = self.check(environment)
        return s

    @abc.abstractmethod
    def render(self, environment=None, debug=False) -> 'str':
        pass

    @abc.abstractmethod
    def __eq__(self, value):
        pass

    @abc.abstractmethod
    def subterms(self):
        """
        this function obtains all subterms in this term, it has to satisfy that
        t.subterms_subst(t.subterms()) == t
        """
        pass

    @abc.abstractmethod
    def subterms_subst(self, subterms):
        """ this function replace subterms by a given list """
        pass

    def __str__(self) -> 'str':
        if Task.get_current() is not None:
            return self.render(Task.get_current())
        elif Environment.default() is not None:
            return self.render(Environment.default())
        else:
            raise Exception("cannot render a term with no environment specified")

    def __repr__(self):
        return str(self)

    def istype(self, environment=None) -> 'bool':
        if isinstance(self.type(environment), Sort) and self.type(environment).sort is SortEnum.type:
            return True

        return False

    # def side_effect(self, environment, context=[]):
        # """
        # this function locates all sub-terms of `self`, calculating their side effects and return
        # them as a list.

        # if you need to implement a term where side effects come from both itself and its sub-terms,
        # please overwrite side_effect_self instead of side_effect
        # """
        # side_effect = []
        # for t in self.subterms():
            # side_effect += t.side_effect(environment, context=context)

        # side_effect += self.side_effect_self(environment, context=context)
        # return side_effect

    # def side_effect_self(self, environment, context=[]):
        # """
        # overwrite this function to implement side-effects on different terms
        # """
        # return []

    # def unfold(self, environment, context=[]):
        # if self.subterms() == []:
            # return self
        # else:
            # return self.subterms_subst(
                    # list(map(lambda t: t.unfold(environment, context), self.subterms()))
                    # )

    def get_comment(self):
        if self.comment is None or self.comment == "":
            return ""
        return "(* %s *)" % self.comment

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
    def __init__(self, sort: 'SortEnum', univ: 'Universe' = None):
        Term.__init__(self)

        self.sort = sort
        self.univ = univ

        if self.sort is SortEnum.type:
            assert self.univ is not None, "types should always declared with universes"

    def type(self, environment=None) -> 'Term':
        if self.sort is SortEnum.prop:
            return Sort(SortEnum.type, Universe.from_level(NativeLevels.Prop(), 1))
        if self.sort is SortEnum.set:
            return Sort(SortEnum.type, Universe.from_level(NativeLevels.Set(), 1))
        else:
            return Sort(SortEnum.type, univ=self.univ + 1)

    def check(self, environment=None) -> 'Term * set(LevelConstraint)':
        return self.type(environment), set()

    def render(self, environment=None, debug=False) -> 'str':
        return self.sort.value + \
                ("@{%s}" % self.univ if self.univ is not None else "")

    def __le__(self, srt):
        """
        this function returns a set of side effects as level constraints
        """
        l, r = self, srt
        if l.sort is not SortEnum.type and r.sort is SortEnum.type:
            """
            Set <= Type, Prop <= Type
            """
            return set()
        elif l.sort == r.sort == SortEnum.type:
            return l.univ <= r.univ
        elif l.sort == r.sort:
            """
            Set <= Set, Prop <= Prop
            """
            return set()
        else:
            raise TypeError

    def __eq__(self, value):
        return isinstance(value, Sort) and value.sort == self.sort

    def subterms(self):
        return []

    def subterms_subst(self, subterms):
        """ sort contains no sub-term and hence cannot be substituted """
        return self


    # singeleton instances
    prop = None
    set = None

    @classmethod
    def mkProp(cls):
        if cls.prop is None:
            cls.prop = Sort(SortEnum.prop)

        return cls.prop

    @classmethod
    def mkSet(cls):
        if cls.set is None:
            cls.set = Sort(SortEnum.set)

        return cls.set

    @classmethod
    def mkType(cls, univ: 'Universe'):
        return Sort(SortEnum.type, univ)

class Cast(Term):

    def __init__(self, body: 'Term', cast_kind: 'int', guaranteed_type: 'Term'):
        Term.__init__(self)

        # cast_kind is a hash
        # 0 - VMcast, 1 - NATIVEcast, 2 - DEFAULTcast, 3 - REVERTcast
        # IMPORTANT! it must be consistent with the coq serializer
        self.body = body
        self.cast_kind = cast_kind
        self.guaranteed_type = guaranteed_type

    def type(self, environment=None) -> 'Term':
        return self.guaranteed_type

    def check(self, environment=None):
        term_type, term_side_effect = self.body.check(environment)
        _, guaranteed_side_effect = self.guaranteed_type.check(environment)


        def is_subtype(l, r):
            """
            return a set of side effects if l < r and raise Exception otherwise
            """

            # the old codes
            # if all_are_same_instances((l, r), Sort):
                # return (l <= r)
            # elif isinstance(l, Const):
                # return is_subtype(l.unfold(environment, context), r)
            # elif isinstance(r, Const):
                # return is_subtype(l, r.unfold(environment, context))
            # else:
                # raise Exception("unimplemented subtyping %s : %s" % (l.render(environment, context), r.render(environment, context)))

            # rawl, rawr = l, r
            typing_counter = 0
            # print("subtyping %s and %s" % (l.render(environment, context), r.render(environment, context)))

            while not isinstance(l, Sort) or not isinstance(r, Sort) or l.sort != SortEnum.type or r.sort != SortEnum.type:
                l, r = l.type(environment), r.type(environment)
                typing_counter += 1

            # print("subtyping %s and %s" % (l.render(environment, context), r.render(environment, context)))
            # FIXME define equality here?
            if l.univ.exprs == r.univ.exprs:
                # the two universes are literally equal
                return set()

            if not l.univ.singleton() or not r.univ.singleton():
                print("WARN: cannot check subtyping relation between joint levels: %s, %s" % (l, r))
                return set()

            # FIXME double check the correctness

            return l.univ <= r.univ

        return self.guaranteed_type, set.union(
                is_subtype(term_type, self.guaranteed_type),
                term_side_effect,
                guaranteed_side_effect
                )

    def render(self, environment=None, debug=False) -> 'str':
        # FIXME
        kind_strs = [ "<:", "<<:", ":", "???" ]
        return "%s %s %s" % (
                self.body.render(environment, debug),
                kind_strs[self.cast_kind],
                self.guaranteed_type.render(environment, debug)
                )

    def __eq__(self, value):
        return isinstance(value, Cast) and \
                self.body == value.body and \
                self.guaranteed_type == value.guaranteed_type

    # def side_effect_self(self, environment, context=[]):
        # type_unfold = self.body.type(environment, context=context).unfold(environment, context)
        # guaranteed_type_unfold = self.guaranteed_type.unfold(environment, context)
        # return (type_unfold.univ <= guaranteed_type_unfold.univ)

    def subterms(self):
        return [self.body, self.guaranteed_type]

    def subterms_subst(self, subterms):
        return Cast(subterms[0], self.cast_kind, subterms[1])


class Const(Term):
    def __init__(self, name: 'str', univ_inst: int = None):
        Term.__init__(self)

        self.name = name

        # universe_instances exist in three types of terms: Const, Ind and Construct
        # it seems that they are used only when the corresponding constant and inductive
        # is defined by the Polymorphic keyword
        if univ_inst is None:
            self.univ_inst = UniverseInstance([])
        else:
            self.univ_inst = univ_inst

    def type(self, environment=None) -> 'Term':
        if environment is None:
            environment = Environment.default()
            if environment is None:
                raise Exception("cannot typing a term with no environment specified")

        consts = environment.constant(self.name)
        if len(consts) > 0:
            const = consts[0]
        else:
            raise TypeError("constant %s not found in the given environment" % self.name)

        return const.type(environment)

    def check(self, environment=None):
        # we assume that when a const is defined, all its side-effects should
        # have been added to the environment
        return self.type(environment,), set()

    def render(self, environment=None, debug=False) -> 'str':
        if environment is None:
            environment = Environment.default()
            if environment is None:
                raise Exception("cannot typing a term with no environment specified")

        found = False
        univ_inst_str = str(self.univ_inst)

        try:
            _ = environment.constant(self.name)[0]
            found = True
        except IndexError:
            pass

        if not debug and found:
            # for Coq.Init.Peano.gt we only return `gt`
            # if debug mode is not activated
            return self.name.split('.')[-1] + univ_inst_str
        else:
            return self.name + univ_inst_str

    def __eq__(self, value):
        return isinstance(value, Const) and self.name == value.name

    def subterms(self):
        return []

    def subterms_subst(self, subterms):
        return self

    def unfold(self, environment=None):
        if environment is None:
            environment = Environment.default()
            if environment is None:
                raise Exception("cannot typing a term with no environment specified")

        consts = environment.constant(self.name)
        if len(consts) > 0:
            const = consts[0]
        else:
            raise TypeError("constant %s not found in the given environment" % self.name)

        return const.body


class Case(Term):
    # TODO not finished yet!!
    def __init__(self, term_matched, term_type, cases):
        Term.__init__(self)

        self.term_matched = term_matched
        self.term_type = term_type
        self.cases = cases

    @classmethod
    def from_json(cls, json_item):
        term_matched = Term.from_json(json_item['term_matched'])
        term_type = Term.from_json(json_item['term_type'])
        cases = list(map(
            Term.from_json, json_item['cases']
            ))

        return cls(term_matched, term_type, cases)

    def type(self, environment=None) -> 'Term':
        raise Exception('unimplemented')

    def check(self, environment=None) -> 'Term':
        raise Exception('unimplemented')

    def render(self, environment=None, debug=False) -> 'str':
        return "(match %s with %s end)" % (
                self.term_matched.render(environment),
                " | ".join(
                    map(lambda t: t.render(environment), self.cases)
                    )
                )

    def __eq__(self, value):
        return False

    def subterms(self):
        return []

    def subterms_subst(self, subterms):
        return self


class Evar(Term):
    # TODO not finished yet!!
    def __init__(self):
        Term.__init__(self)

        pass

    def type(self, environment=None) -> 'Term':
        raise Exception('unimplemented')

    def check(self, environment=None) -> 'Term':
        raise Exception('unimplemented')

    def render(self, environment=None, debug=False) -> 'str':
        return 'EVAR'

    def __eq__(self, value):
        return False

    def subterms(self):
        return []

    def subterms_subst(self, subterms):
        return self


class Var(Const):

    def type(self, environment=None) -> 'Term':
        if environment is None:
            environment = Environment.default()
            if environment is None:
                raise Exception("cannot typing a term with no environment specified")

        vars = environment.variable(self.name)
        if len(vars) > 0:
            var = vars[0]
        else:
            raise TypeError("variable %s not found in the given environment" % self.name)

        return var.type(environment)

    def check(self, environment=None):
        return self.type(environment), set()

    def render(self, environment=None, debug=False) -> 'str':
        univ_inst_str = str(self.univ_inst)
        return self.name + univ_inst_str


class Rel(Term):
    def __init__(self, index: int):
        Term.__init__(self)

        # all indexes in holboost must start from zero !!!!!!
        self.index = index

    def type(self, environment=None) -> 'Term':
        binding = environment.rel(self.index)
        if binding is None:
            raise TypingUnclosedError()

        if binding.type is None:
            if binding.value is not None:
                return binding.value.type(environment.inherited_environment)
            else:
                raise TypeError

        return binding.type

    def check(self, environment=None):
        return self.type(environment), set()

    def render(self, environment=None, debug=False) -> 'str':
        try:
            binding = None if environment is None else environment.rel(self.index)
        except IndexError:
            binding = None

        if binding is None or binding.name is None or debug:
            return "_REL_%d_" % self.index
        else:
            return binding.name

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
        Term.__init__(self)

        self.func = func
        self.args = args

    def type(self, environment=None) -> 'Term':
        # if the type of func is A -> B -> C and there are two arguments, then the type of the whole term
        # should be C
        # if there is only one argument, it should be B -> C
        # ..

        typ = self.func.type(environment)
        for _ in range(len(self.args)):
            while isinstance(typ, Const):
                typ = typ.unfold(environment)

            typ = typ.body

        # if there are no rel variables in `typ`, that's it
        # otherwise it is a dependent type
        # in this case we will replace the rels in the type term with the arguments applied to this function

        return typ.rels_subst(self.args)

    def check(self, environment=None):
        typ, side_effects = self.func.check(environment)

        env = environment
        for arg in self.args:
            while isinstance(typ, Const):
                typ = typ.unfold(environment)

            # print("CHECKING", arg, "BINDING", bindings)
            if isinstance(typ, Prod):
                """
                if f : A -> B is applied to a, i.e. (f a), we need to make sure (a : A)
                """
                side_effects.update(Cast(arg, 0, typ.arg_type).side_effects(env))

                env = ContextEnvironment(Binding(None, arg, None), env)
                typ = typ.body
            else:
                raise TypingUnclosedError("cannot apply %s to %s" % (typ.render(environment), arg.render(environment)))

        return typ.rels_subst(self.args), side_effects



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

    def subterms_subst(self, subterms):
        return Apply(*subterms)


class ContextTerm(Term):
    def __init__(self, arg_name: 'str', arg_type: 'Term', body: 'Term'):
        Term.__init__(self)

        self.arg_name = arg_name
        self.arg_type = arg_type
        self.body = body


class Prod(ContextTerm):
    def type(self, environment=None) -> 'Term':
        """
        please refer to https://coq.inria.fr/distrib/current/refman/language/cic.html
        for the typing rules
        """
        body_type = self.body.type(ContextEnvironment(Binding(self.arg_name, None, self.arg_type), environment))
        assert isinstance(body_type, Sort)
        if body_type.sort is SortEnum.prop:
            return body_type
        else:
            type_of_arg_type = self.arg_type.type(environment)
            assert isinstance(type_of_arg_type, Sort)
            if body_type.sort is SortEnum.set:
                if type_of_arg_type is SortEnum.prop or type_of_arg_type is SortEnum.set:
                    return body_type
                else:
                    return type_of_arg_type
            else:
                return Sort.mkType(
                        Universe.union(body_type.univ, type_of_arg_type.univ)
                        )

    def check(self, environment=None):
        # we need to check everything for correct generation of side effect
        body_type, body_sideff = self.body.check(ContextEnvironment(Binding(self.arg_name, None, self.arg_type), environment))
        type_of_arg_type, type_of_arg_sideff = self.arg_type.check(environment)

        sideff = set.union(body_sideff, type_of_arg_sideff)
        assert isinstance(body_type, Sort)
        if body_type.sort is SortEnum.prop:
            return body_type, sideff
        else:
            assert isinstance(type_of_arg_type, Sort), "type_of_arg_type %s: %s" % (self.arg_type, type_of_arg_type)
            if body_type.sort is SortEnum.set:
                if type_of_arg_type is SortEnum.prop or type_of_arg_type is SortEnum.set:
                    return body_type, sideff
                else:
                    return type_of_arg_type, sideff
            else:
                return Sort.mkType(Universe.union(body_type.univ, type_of_arg_type.univ)), sideff

    def render(self, environment=None, debug=False) -> 'str':
        if self.arg_name is None:
            # arrow form
            return "{0} -> {1}".format(
                    self.arg_type.render(environment, debug),
                    self.body.render(ContextEnvironment(Binding(self.arg_name, None, self.arg_type), environment), debug))
        else:
            # forall form
            # combine multiple foralls if possible
            return "forall {0}: {1}, {2}".format(
                    self.arg_name,
                    self.arg_type.render(environment, debug),
                    self.body.render(ContextEnvironment(Binding(self.arg_name, None, self.arg_type), environment), debug)
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

    def type(self, environment=None, ) -> 'Term':
        return self.body.type(ContextEnvironment(Binding(self.arg_name, self.arg_body, self.arg_type), environment))

    def check(self, environment=None, context=[]):
        body_typ, body_sideff = self.body.check(
            ContextEnvironment(Binding(self.arg_name, self.arg_body, self.arg_type), environment)
            )
        _, arg_sideff = self.arg_type.check(environment)
        return body_typ, set.union(
                body_sideff,
                arg_sideff,
                Cast(self.arg_body, 0, self.arg_type).side_effects(environment)
                )

    def render(self, environment=None, debug=False) -> 'str':
        return "let {0} : {1} := {2} in {3}".format(
                self.arg_name,
                self.arg_type.render(environment, debug),
                self.arg_body.render(environment, debug),
                self.body.render(ContextEnvironment(Binding(self.arg_name, self.arg_body, self.arg_type), environment), debug)
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

    def type(self, environment=None) -> 'Term':
        return Prod(None, self.arg_type, self.body.type(
            ContextEnvironment(Binding(self.arg_name, None, self.arg_type), environment)
            )
        )

    def check(self, environment=None):
        _, arg_sideff = self.arg_type.check(environment)
        body_typ, body_sideff = self.body.check(ContextEnvironment(Binding(self.arg_name, None, self.arg_type), environment))
        return Prod(None, self.arg_type, body_typ), set.union(arg_sideff, body_sideff)

    def render(self, environment=None, debug=False) -> 'str':
        return "fun ({0}: {1}) => {2}".format(
                self.arg_name if self.arg_name is not None else "_",
                self.arg_type.render(environment, debug),
                self.body.render(ContextEnvironment(Binding(self.arg_name, None, self.arg_type), environment), debug)
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
    def __init__(self, mutind: 'str', ind_index: int, constructor_index: int, univ_inst = None):
        Term.__init__(self)

        self.mutind_name = mutind
        self.ind_index = ind_index
        self.constructor_index = constructor_index
        if univ_inst is None:
            self.univ_inst = UniverseInstance([])
        else:
            self.univ_inst = univ_inst

    def type(self, environment=None) -> 'Term':
        if environment is None:
            environment = Environment.default()
            if environment is None:
                raise TypeError("cannot typing a term with no environment specified")

        mutinds = environment.mutind(self.mutind_name)
        if len(mutinds) > 0:
            mutind = mutinds[0]
        else:
            raise TypeError("mut-inductive %s does not belong to the given environment" % self.mutind_name)

        return mutind.inds[self.ind_index].constructors[self.constructor_index].type(environment)

    def check(self, environment=None):
        return self.type(environment), set()

    def render(self, environment=None, debug=False) -> 'str':
        if environment is None:
            environment = Environment.default()
            if environment is None:
                raise Exception("cannot typing a term with no environment specified")

        found = False
        construct_name = None

        mutinds = environment.mutind(self.mutind_name)
        if len(mutinds) > 0:
            mutind = mutinds[0]
            construct_name = mutind.inds[self.ind_index].constructors[self.constructor_index].name
            found = True


        univ_inst_str = str(self.univ_inst)
        if not debug and found:
            return construct_name + univ_inst_str
        else:
            return '_%s_%d_%d_' % (self.mutind_name, self.ind_index, self.constructor_index) + univ_inst_str

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
    def __init__(self, mutind: 'str', ind_index: int, univ_inst: int = None):
        Term.__init__(self)

        self.mutind_name = mutind
        self.ind_index = ind_index
        if univ_inst is None:
            self.univ_inst = UniverseInstance([])
        else:
            assert(isinstance(univ_inst, UniverseInstance))
            self.univ_inst = univ_inst

    def type(self, environment=None) -> 'Term':
        if environment is None:
            environment = Environment.default()
            if environment is None:
                raise Exception("cannot typing a term with no environment specified")

        mutinds = environment.mutind(self.mutind_name)
        if len(mutinds) > 0:
            mutind = mutinds[0]
        else:
            raise TypeError("mut-inductive %s does not belong to the given environment" % self.mutind_name)

        return mutind.inds[self.ind_index].type(environment)

    def check(self, environment=None):
        return self.type(environment), set()

    def render(self, environment=None, debug=False) -> 'str':
        if environment is None:
            environment = Environment.default()
            if environment is None:
                raise Exception("cannot typing a term with no environment specified")

        univ_inst_str = str(self.univ_inst)

        try:
            mutind = environment.mutind(self.mutind_name)[0]
        except IndexError:
            mutind = None

        if not debug and mutind is not None:
            return mutind.inds[self.ind_index].name + univ_inst_str
        else:
            return '_%s_%d_' % (self.mutind_name, self.ind_index) + univ_inst_str

    def __eq__(self, value):
        return isinstance(value, Ind) and \
                value.mutind_name == self.mutind_name and \
                value.ind_index == self.ind_index

    def subterms(self):
        return []

    def subterms_subst(self, subterms):
        return self
