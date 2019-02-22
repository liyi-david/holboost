from kernel.term import *
from lib.common import *
from lib.top import Top

from .pattern import *


class MatchFailure(Exception):
    def __init__(self, pat, term):
        self.pat = pat
        self.term = term

class MatchResult:

    class OneMatchResult:
        def __init__(self, pattern, matched, metavar_map, alias_map):
            self.pattern = pattern
            self.matched = matched
            self.metavar_map = metavar_map
            self.alias_map = alias_map

        def render(self, environment=None):
            return "pattern %s matched with %s, where %s" % (
                    self.pattern.render(environment),
                    self.matched.render(environment),
                    ", ".join([ "?%s = %s" % (name, self.metavar_map[name].render(environment)) for name in self.metavar_map ])
                    )

        def __str__(self): return self.render()


    def __init__(self, term):
        self.term = term
        # each match is a 3-tuple (pattern, matched, patvar_map)
        self.matches = []
    def __add__(self, result_or_tuple):
        raise Exception('unimplemented')

    def __iadd__(self, result_or_tuple):
        if isinstance(result_or_tuple, MatchResult):
            assert result.term is result_or_tuple.term, \
                "match results can be added only when the terms being matched are exactly the same!"

            self.matches += result_or_tuple.matches
        elif isinstance(result_or_tuple, MatchResult.OneMatchResult):
            self.matches.append(result_or_tuple)
        else:
            self.matches.append(MatchResult.OneMatchResult(*result_or_tuple))

        return self

    def index_by_matched(self, t: 'Term') -> int:
        # FIXME this will be extremely slow
        for onematch in self:
            if onematch.matched is t:
                return self.matches.index(onematch)

        return None

    def render(self, environment=None):
        return "\n".join(
                map(lambda oneresult: oneresult.render(environment), self.matches)
                )

    def __str__(self): return self.render()

    def __iter__(self): return iter(self.matches)



def match_at(pattern, term, environment=None, top=None):
    metavar_matched = {}
    alias_matched = {}

    def try_match(pattern, term):
        if top is not None:
            top.debug("match", 'matching %s in %s' % (pattern, term))

        if isinstance(pattern, Meta):
            if pattern.index in metavar_matched:
                if metavar_matched[pattern.index] == term:
                    return
                else:
                    # the same meta variable unfortunately matches
                    # two different terms
                    raise MatchFailure(pattern, term)
            else:
                # we got a match !
                # but only after the type check ...
                if pattern.typ is not None:
                    if environment is None:
                        raise Exception("no environment is given when performing typed pattern-match processes")

                    # FIXME double check
                    try:
                        try_match(pattern.typ, term.type(environment))
                    except TypingUnclosedError:
                        raise MatchFailure(pattern, term)

                metavar_matched[pattern.index] = term
        elif isinstance(pattern, Alias):
            try_match(pattern.sub_pattern, term)
            alias_matched[pattern.alias] = term
        elif isinstance(pattern, Cast):
            try_match(pattern.body, term)
        # for some non-recursive term, we simply need them to be equal
        elif all_are_same_instances((pattern, term), (Sort, Const, Var, Rel, Construct, Ind)):
            if pattern != term:
                raise MatchFailure(pattern, term)
        elif all_are_same_instances((pattern, term), (Lambda, LetIn, Prod)):

            # Liyi: I removed the name checking since I think that is not important
            # and should not make the matching result different
            # if pattern.arg_name != term.arg_name:
            #    raise MatchFailure(pattern, term)

            try_match(pattern.arg_type, term.arg_type)
            try_match(pattern.body, term.body)
            if isinstance(pattern, LetIn):
                try_match(pattern.arg_body, term.arg_body)
        elif all_are_same_instances((pattern, term), (Apply)):
            try_match(pattern.func, term.func)

            if len(pattern.args) != len(term.args):
                raise MatchFailure(pattern, term)

            for i in range(len(pattern.args)):
                try_match(pattern.args[i], term.args[i])
        else:
            raise MatchFailure(pattern, term)

    try:
        try_match(pattern, term)
        return MatchResult.OneMatchResult(pattern, term, metavar_matched, alias_matched)
    except MatchFailure:
        top.debug("match", "matching failed.")
        return None


def match(patterns, term, match_subterm=False, environment=None, top=None):
    """
    @patterns: can be either a single pattern or a list of patterns
    @term: the term to match
    @match_subterm: if set to True, then match all subterms of term
    """
    top.debug('match', 'matching start.')
    if isinstance(patterns, Term):
        patterns = [ patterns ]

    patterns = list(patterns)

    if environment is None:
        environment = Environment.default()

    if top is None:
        top = Top.default()

    match_result = MatchResult(term)

    def iterate(patterns, term):
        nonlocal match_result
        for pattern in patterns:
            result = match_at(pattern, term, environment=environment, top=top)

            # here it is import not to iterate on subterms when we have a match on
            # the current term. otherwise matches may intersect and leads to unexpected
            # problems when replacing the matched parts
            if result is not None:
                match_result += result
                return

        # if multiple patterns successfully match the same term, only one of them will show
        # up in the final result

        # iterate on the sub-terms
        for subterm in term.subterms():
            iterate(patterns, subterm)

    iterate(patterns, term)
    return match_result


