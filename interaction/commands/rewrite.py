from proving.pattern.match import *
from proving.tactics.rewrite import *

from .command import Command


class RewriteCommand(Command):

    class RewriteHint:
        def __init__(self, type: 'Term', lemma: 'Term', right2left: 'bool'):
            self.type = type
            self.lemma = lemma
            self.right2left = right2left

            # extract context and equality, e.g.
            # forall n:nat, n = n ->   n:nat    (n - 1) + 1 = n
            #                        (context)    (equality)
            self.context, self.equality = obtain_equality(self.type)
            self.equality = from_rels(self.context, self.equality)
            # pat_left : (?1 - 1) + 1, pat_right : ?1
            self.pat_left, self.pat_right = self.equality.args[1], self.equality.args[2]

            print("pattern of %s : %s -> %s" % (self.lemma, self.pat_left, self.pat_right))

    def __init__(self, hints, task=None):
        self.hints = hints
        self.task = task
        self.left_pat_map = {}
        for hint in self.hints:
            self.left_pat_map[id(hint.pat_left)] = hint

    def get_hint_by_left_pattern(self, pat):
        return self.left_pat_map[id(pat)]

    def run(self, top):
        top.print('rewriting starts.')
        patterns = list(map(lambda hint: hint.pat_left, self.hints))

        match_result = match(patterns, self.task.goal, match_subterm=True, environment=self.task)
        # FIXME
        top.namespace['result'] = match_result

        # now let us construct the proof-term to apply
        # the basic idea is, if we wanna replace a with b, c with d, then first construct a proof
        # for a, b = c, d

        # the first thing is to generate the equality proof of the tuple
        proof = None
        for one_match in match_result.matches:
            hint = self.get_hint_by_left_pattern(one_match.pattern)

            eq_hyp_args = reversed([one_match.metavar_map[i] for i in range(len(hint.context))])
            eq_hyp = Apply(hint.lemma, *eq_hyp_args)
            top.print("eq hypothesis: ", eq_hyp.type(self.task).render(self.task))

        # this maps id of a sub-term to a match result (if exists)
        def replace(context, term):
            subterms = term.subterms()
            for i in range(len(subterms)):
                if id(subterms[i]) in match_result_map:
                    subterms[i] = Rel(len(context) + len(additional_context))
                    # FIXME at least term and type
                    additional_context.append('NAME')
                    # FIXME appliedto?
                    appliedto.append(Const('wtf'))
                else:
                    # only in the last term we add new context
                    if isinstance(term, ContextTerm) and i == len(subterms) - 1:
                        subterms[i] = replace(context + [term], subterms[i])
                    else:
                        subterms[i] = replace(context, subterms[i])

