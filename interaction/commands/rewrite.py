from kernel.term import *
from kernel.environment import ContextEnvironment

from plugins.basic.patternmatching import *

from .command import Command


def tuple_nth(t: Term, n: int, typ: Term = None) -> Term:

    """
    this function automatically generates the nth operator based on a set
    of fst/snd operations
    """

    fst = Const("Coq.Init.Datatypes.fst")
    snd = Const("Coq.Init.Datatypes.snd")
    pair = Construct("Coq.Init.Datatypes.prod", 0, 0)
    prod = Ind("Coq.Init.Datatypes.prod", 0)

    is_tuple = False
    if typ is not None:
        is_tuple = isinstance(typ, Apply) and typ.func == prod
    else:
        is_tuple = isinstance(t, Apply) and t.func == pair

    if is_tuple:
        fst_type, snd_type = (t if typ is None else typ).args[0:2]
        if n == 0:
            # in this case we are obtaining a middle element in the tuple
            return Apply(fst, fst_type, snd_type, t)
        else:
            return tuple_nth(
                    Apply(snd, fst_type, snd_type, t),
                    n - 1,
                    snd_type
                    )
    else:
        assert n == 0, "you can only obtain the 0th element in a non-tuple"
        return t

def is_equality_relation(term):
    # according to coq's implementation, there are two types of equality, they are
    # setoid equality and leibniz equality
    if isinstance(term, Ind):
        # for leibniz equality
        # FIXME
        return term.mutind_name == "Coq.Init.Logic.eq"

    return False

def obtain_equality(term):
    """
    given a term in form of:

        forall a, forall b, forall c, .... = ....
        ~~~~~~~~~~~~~~~~~~~~~~~~~~~~  ~~~~~~~~~~~
                   context              equality

    the function separates the context part and the equality part
    """
    context = None

    while term is not None:
        if isinstance(term, Apply) and is_equality_relation(term.func):
            return context, term
        elif isinstance(term, Prod):
            context = ContextEnvironment(Binding.from_term(term), context)
            term = term.body
        else:
            raise Exception("no equality found in %s" % str(term))


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
            print(self.type, "\n", self.context, "\n", self.equality)
            self.equality = from_rels(self.context, self.equality)
            # pat_left : (?1 - 1) + 1, pat_right : ?1
            self.pat_left, self.pat_right = self.equality.args[1], self.equality.args[2]

            # print("pattern of %s : %s -> %s" % (self.lemma, self.pat_left, self.pat_right))

    def __init__(self, hints):
        self.hints = hints
        self.left_pat_map = {}
        for hint in self.hints:
            self.left_pat_map[id(hint.pat_left)] = hint

        Command.__init__(self)

    def get_hint_by_left_pattern(self, pat):
        return self.left_pat_map[id(pat)]

    def run(self, top):
        patterns = list(map(lambda hint: hint.pat_left, self.hints))

        for pat in patterns:
            top.debug("rewrite", "left pattern: ", pat.render(self.task))

        match_result = match(patterns, self.task.goal, match_subterm=True, environment=self.task, top=top)

        top.debug("rewrite", "match finished.")

        # now let us construct the proof-term to apply
        # the basic idea is, if we wanna replace a with b, c with d, then first construct a proof
        # for a, b = c, d

        # the first thing is to generate the equality proof of the tuple
        # pair_eq: T1, T2, (a b:T1) (c d:T2) a = b -> c = d -> (a, d) = (b, d)
        # the proof is located in coq-plugin/theory/plugin.v
        pair_eq = Const('Holboost.plugin.pair_eq')
        proof = None

        if len(match_result.matches) is 0:
            # no match found, failed to rewrite
            return None

        # it is important to use reversed here, since a pair (a, b, c) is actually constructed as
        # (a, (b, c)) in coq, so first we prove that b, c = b', c' instead of a and a'
        for one_match in reversed(match_result.matches):
            hint = self.get_hint_by_left_pattern(one_match.pattern)

            # TODO: find why the args are reversed???
            eq_hyp_args = [one_match.metavar_map[i] for i in range(hint.context.length())]
            eq_hyp_args.reverse()
            eq_hyp = Apply(hint.lemma, *eq_hyp_args)
            top.debug("rewrite", "eq hypothesis: ", eq_hyp.render(self.task))

            # we always assume that type of the proof is ... = ...
            if proof is None:
                proof = eq_hyp
            else:
                eq_hyp_type = eq_hyp.type(self.task)
                proof_type = proof.type(self.task)
                proof = Apply(
                            pair_eq,
                            eq_hyp_type.args[0],
                            proof_type.args[0],
                            eq_hyp_type.args[1], eq_hyp_type.args[2],
                            proof_type.args[1], proof_type.args[2],
                            eq_hyp,
                            proof
                            )

        # top.print("final eq hypothesis: ", proof.type(self.task).render(self.task))
        # top.namespace['proof'] = proof

        # assuming we need to replace a0, a1, ..., an with b0, ...., bn
        # in the final proof lemma forall T: Type, forall a: T, forall b: T, forall P: T -> Prop, (eq T a b) -> (P b) -> (P a)
        # now we have:
        # - T, a, b (eq T a b) from proof
        # now we need to construct P as follows

        # extract the required variables
        Ttuple, a, b = proof.type(self.task).args

        # this maps id of a sub-term to a match result (if exists)
        def replace(context_len, term):
            subterms = term.subterms()
            for i in range(len(subterms)):
                index = match_result.index_by_matched(subterms[i])
                if index is not None:
                    subterms[i] = tuple_nth(Rel(context_len), index, Ttuple)
                else:
                    subterms[i] = replace(
                            context_len + (1 if isinstance(term, ContextTerm) else 0),
                            subterms[i]
                            )

            return term.subterms_subst(subterms)

        P = Lambda("__VAR_TUPLE", Ttuple, replace(0, self.task.goal))
        # construct the final term to apply
        partial_proof = Apply(
                Const("Holboost.plugin.rewrite_l2r"),
                Ttuple, a, b, P, proof
                )

        top.debug_namespace['rewrite_proof'] = partial_proof

        top.debug("rewrite", "Ttuple   : ", Ttuple.render(self.task))
        top.debug("rewrite", "a        : ", a.render(self.task))
        top.debug("rewrite", "b        : ", b.render(self.task))
        top.debug("rewrite", "P        : ", P.render(self.task))
        top.debug("rewrite", "eq_proof : ", proof.render(self.task))

        top.debug("rewrite", "proof    : ", partial_proof.render(self.task))
        top.debug("rewrite", "prf type : ", partial_proof.type(self.task).render(self.task))

        _, sideff = partial_proof.check(self.task)

        result = {
                "proof": partial_proof.to_json(),
                "sideff": list(map(lambda uc: uc.to_json(), sideff))
                }

        return result
