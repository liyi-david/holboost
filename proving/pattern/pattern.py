from kernel.term import *

"""
a pattern is also a term, but it may contains
- meta variables
- aliases
"""

class PatternAbuse(Exception):
    pass

class Meta(Term):
    def __init__(self, index):
        """
        index can be any hashable objects, including but not limited within : int, str, etc.
        index can be None
        """
        self.index = index

    def type(self):
        raise PatternAbuse("type of patterns cannot be evaluated")

    def export(self, environment=None, debug=False):
        return "?%s" % ("_" if self.index is None else self.index)

    def __eq__(self, value):
        raise PatternAbuse()


class Alias(Term):
    def __init__(self, alias: 'str', sub_pattern: 'Term'):
        """
        an `alias` is similar to a `group` in commonly-used regexes, it matches a subpattern and take the
        whole match as part of the result. Coq's pattern matching interface does not provide this feature.
        """
        self.alias = alias
        self.sub_pattern = sub_pattern

    def type(self):
        raise PatternAbuse("type of patterns cannot be evaluated")

    def export(self, environment=None, debug=False):
        return "(%s) as ?%s" % (self.sub_pattern.export(environment, debug), self.alias)

    def __eq__(self, value):
        raise PatternAbuse()


def from_rels(term):

    def generate(depth, term):
        # TODO write an explanation on depth

        if isinstance(term, Prod):
            return Prod(
                    term.arg_name,
                    generate(depth, term.arg_type),
                    generate(depth + 1, term.body_type)
                    )
        elif isinstance(term, Lambda):
            return Lambda(
                    term.arg_name,
                    generate(depth, term.arg_type),
                    generate(depth + 1, term.body)
                    )
        elif isinstance(term, LetIn):
            return LetIn(
                    term.arg_name,
                    generate(depth, term.arg_type),
                    generate(depth, term.arg_body),
                    generate(depth + 1, term.body)
                    )
        elif isinstance(term, (Sort, Const, Construct, Ind)):
            return term
        elif isinstance(term, Rel):
            if term.index >= depth:
                return Meta(term.index - depth)
            else:
                return term
        elif isinstance(term, Apply):
            return Apply(
                    generate(depth, term.func),
                    *[ generate(depth, arg) for arg in term.args ]
                    )
        else:
            raise Exception("cannot generate pattern from %s" % term)

    return generate(0, term)
