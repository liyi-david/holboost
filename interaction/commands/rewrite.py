from kernel.term import *
from kernel.environment import ContextEnvironment

from plugins.basic.patternmatching import *
from plugins.theories.product import tuple_nth
from .command import Command


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
        def __init__(self, type: 'Term', lemma: 'Term', left2right: 'bool'):
            self.type = type
            self.lemma = lemma
            self.left2right = left2right

            # extract context and equality, e.g.
            # forall n:nat, n = n ->   n:nat    (n - 1) + 1 = n
            #                        (context)    (equality)
            self.context, self.equality = obtain_equality(self.type)
            self.equality = from_rels(self.context, self.equality)
            # pat_left : (?1 - 1) + 1, pat_right : ?1
            self.pat_left, self.pat_right = self.equality.args[1], self.equality.args[2]

            # print("pattern of %s : %s -> %s" % (self.lemma, self.pat_left, self.pat_right))

        def get_pattern(self, reversed=False):
            if self.left2right:
                return self.pat_left
            else:
                return self.pat_right

    # ======= functions of RewriteCommand =======

    def __init__(self, hints, target):
        Command.__init__(self)

        self.hints = hints
        self.pat_map = {}
        self.target = target
        for hint in self.hints:
            self.pat_map[id(hint.pat_left)] = hint
            self.pat_map[id(hint.pat_right)] = hint

    def __str__(self):
        target = "goal" if self.target is None else self.target
        return "boom autorewrite [%s] with hints [%s]" % (
                target,
                ", ".join(map(lambda h: str(h.lemma), self.hints))
                )


    def get_hint_by_pattern(self, pat):
        return self.pat_map[id(pat)]

    @classmethod
    def from_json(cls, json_item):
        return RewriteCommand(
                list(
                    map(
                        lambda hintrec : RewriteCommand.RewriteHint(
                            Term.from_json(hintrec['type']),
                            Term.from_json(hintrec['lemma']),
                            hintrec['left2right']
                        ),
                        json_item['hints']
                    )
                ),
                None if 'in' not in json_item else json_item['in']
            )

    def rewrite_single_formula(self, name, formula, top):
        # when name != __goal__, the current formula is one of the hypothesises
        # in local variables
        patterns = list(map(lambda h: h.get_pattern(reversed=(name != "__goal__")), self.hints))

        for pat in patterns:
            top.debug("rewrite", "pattern: ", pat.render(self.task))

        match_result = match(patterns, formula, match_subterm=True, environment=self.task, top=top)

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
            top.debug("rewrite", "match", one_match)
            hint = self.get_hint_by_pattern(one_match.pattern)

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

        P = Lambda("__VAR_TUPLE", Ttuple, replace(0, formula))
        # construct the final term to apply
        partial_proof = Apply(
                Const("Holboost.plugin.rewrite_" + ("l2r" if name == "__goal__" else "r2l")),
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
                "target": name,
                "proof": partial_proof.to_json(),
                "sideff": list(map(lambda uc: uc.to_json(), sideff))
                }

        return result


    def run(self, top):
        # TODO store hints in global cache

        if self.target is None:
            formulas = [('__goal__', self.task.goal)]
        elif self.target == '*':
            formulas = map(lambda vdecl: (vdecl[0], vdecl[1].type()), self.task.variables().items())

        resulted_tactics = []
        for name, formula in formulas:
            top.debug("rewrite", "start working on %s: %s" % (name, str(formula)))
            resulted_tactics.append(self.rewrite_single_formula(name, formula, top))

        return resulted_tactics
