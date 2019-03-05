from kernel.term import *
from kernel.environment import ContextEnvironment, EnvironmentOverflow

from lib.top import Top

"""
a pattern is also a term, but it may contains
- meta variables
- aliases
"""

class PatternAbuse(Exception):
    pass

class Meta(Term):
    def __init__(self, index, type=None):
        """
        index can be any hashable objects, including but not limited within : int, str, etc.
        index can be None
        """
        self.index = index
        self.typ = type

    def type(self, environment):
        raise PatternAbuse("type of patterns cannot be evaluated")

    def check(self, environment):
        raise PatternAbuse("type of patterns cannot be evaluated")

    def render(self, environment=None, debug=False):
        return "?(%s: %s)" % ("_" if self.index is None else self.index, self.typ.render(environment, debug))

    def __eq__(self, value):
        raise PatternAbuse()

    def subterms(self):
        raise PatternAbuse()

    def subterms_subst(self, subterms):
        raise PatternAbuse()


class Alias(Term):
    def __init__(self, alias: 'str', sub_pattern: 'Term'):
        """
        an `alias` is similar to a `group` in commonly-used regexes, it matches a subpattern and take the
        whole match as part of the result. Coq's pattern matching interface does not provide this feature.
        """
        self.alias = alias
        self.sub_pattern = sub_pattern

    def type(self, environment):
        raise PatternAbuse("type of patterns cannot be evaluated")

    def check(self, environment):
        raise PatternAbuse("type of patterns cannot be evaluated")

    def render(self, environment=None, debug=False):
        return "(%s) as ?%s" % (self.sub_pattern.render(environment, debug), self.alias)

    def __eq__(self, value):
        raise PatternAbuse()

    def subterms(self):
        raise PatternAbuse()

    def subterms_subst(self, subterms):
        raise PatternAbuse()


def from_rels(outside_context_env, term, top=None):
    if top is None:
        top = Top.default()

    def generate(environment, term):
        top.debug('pattern', 'from rels', environment, term)
        if isinstance(term, Prod):
            return Prod(
                    term.arg_name,
                    generate(environment, term.arg_type),
                    generate(ContextEnvironment(Binding.from_term(term), environment), term.body)
                    )
        elif isinstance(term, Lambda):
            return Lambda(
                    term.arg_name,
                    generate(environment, term.arg_type),
                    generate(ContextEnvironment(Binding.from_term(term), environment), term.body)
                    )
        elif isinstance(term, LetIn):
            return LetIn(
                    term.arg_name,
                    generate(environment, term.arg_type),
                    generate(environment, term.arg_body),
                    generate(ContextEnvironment(Binding.from_term(term), environment), term.body)
                    )
        elif isinstance(term, (Sort, Const, Construct, Ind)):
            return term
        elif isinstance(term, Cast):
            return Cast(
                    generate(environment, term.body),
                    term.cast_kind,
                    generate(environment, term.guaranteed_type)
                    )
        elif isinstance(term, Rel):
            binding = environment.rel(term.index)

            try:
                outside_context, outside_index = outside_context_env.lookup_by_binding(binding)
                # free variable here
                return Meta(
                        outside_index,
                        generate(outside_context.inherited_environment, binding.type)
                        )
            except EnvironmentOverflow:
                return term

        elif isinstance(term, Apply):
            return Apply(
                    generate(environment, term.func),
                    *[ generate(environment, arg) for arg in term.args ]
                    )
        else:
            raise Exception("cannot generate pattern from %s" % term)

    return generate(outside_context_env, term)
