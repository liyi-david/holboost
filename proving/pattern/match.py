from proving.pattern.pattern import *
from kernel.term import *
from lib.common import *

autoload = True

class MatchFailure(Exception):
    pass

class MatchResult:
    pass


def match_at(pattern, term):
    metavar_matched = {}
    alias_matched = {}

    def try_match(pattern, term):
        # print('matching %s in %s' % (pattern, term))
        if isinstance(pattern, Meta):
            if pattern.index in metavar_matched:
                if metevar_matched[pattern.index] == term:
                    return
                else:
                    # the same meta variable unfortunately matches
                    # two different terms
                    raise MatchFailure()
            else:
                # we got a match !
                metavar_matched[pattern.index] = term
        elif isinstance(pattern, Alias):
            try_match(pattern.sub_pattern, term)
            alias_matched[pattern.alias] = term
        # for some non-recursive term, we simply need them to be equal
        elif all_are_same_instances((pattern, term), (Sort, Const, Var, Rel, Construct, Ind)):
            if pattern != term:
                raise MatchFailure()
        elif all_are_same_instances((pattern, term), (Lambda, LetIn, Prod)):
            if pattern.arg_name != term.arg_name:
                raise MatchFailure()

            try_match(pattern.arg_type, term.arg_type)
            try_match(pattern.body, term.body)
            if isinstance(pattern, LetIn):
                try_match(pattern.arg_body, term.arg_body)
        elif all_are_same_instances((pattern, term), (Apply)):
            try_match(pattern.func, term.func)

            if len(pattern.args) != len(term.args):
                raise MatchFailure()

            for i in range(len(pattern.args)):
                try_match(pattern.args[i], term.args[i])

    try:
        try_match(pattern, term)
        print(metavar_matched)
        return MatchResult()
    except MatchFailure:
        return None


def run(pattern, term, subterm=False):
    pass
