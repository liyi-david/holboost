from kernel.term import *

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
        self.type = type

    def type(self, environment, context=[]):
        raise PatternAbuse("type of patterns cannot be evaluated")

    def render(self, environment=None, context=[], debug=False):
        return "?(%s: %s)" % ("_" if self.index is None else self.index, self.type.render(environment, context, debug))

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

    def type(self, environment, context=[]):
        raise PatternAbuse("type of patterns cannot be evaluated")

    def render(self, environment=None, context=[], debug=False):
        return "(%s) as ?%s" % (self.sub_pattern.render(environment, context, debug), self.alias)

    def __eq__(self, value):
        raise PatternAbuse()

    def subterms(self):
        raise PatternAbouse()

    def subterms_subst(self, subterms):
        raise PatternAbuse()


def from_rels(outside_context, term):

    def generate(context, term):
        if isinstance(term, Prod):
            return Prod(
                    term.arg_name,
                    generate(context, term.arg_type),
                    generate(context + [term], term.body_type)
                    )
        elif isinstance(term, Lambda):
            return Lambda(
                    term.arg_name,
                    generate(context, term.arg_type),
                    generate(context + [term], term.body_type)
                    )
        elif isinstance(term, LetIn):
            return LetIn(
                    term.arg_name,
                    generate(context, term.arg_type),
                    generate(context, term.arg_body),
                    generate(context + [term], term.body_type)
                    )
        elif isinstance(term, (Sort, Const, Construct, Ind)):
            return term
        elif isinstance(term, Cast):
            return Cast(
                    generate(context, term.body),
                    term.cast_kind,
                    generate(context, term.guaranteed_type)
                    )
        elif isinstance(term, Rel):
            binding = term.get_binding(context)
            if binding in outside_context:
                # free variable here
                return Meta(outside_context.index(binding), binding.arg_type)
            else:
                return term
        elif isinstance(term, Apply):
            return Apply(
                    generate(context, term.func),
                    *[ generate(context, arg) for arg in term.args ]
                    )
        else:
            raise Exception("cannot generate pattern from %s" % term)

    return generate(outside_context, term)
