from kernel.tactic import Tactic
from kernel.environment import ContextEnvironment
from kernel.term import Lambda, Apply, Ind, Sort, Const, Prod, Binding, Rel
from kernel.proofview import Goal, Proof


class InductionTactic(Tactic):

    @classmethod
    def run(cls, g):
        gf = g.formula()
        env = g.env()

        # TODO apply induction to a prod, instead of a env
        if isinstance(gf, Prod) and isinstance(gf.arg_type, Ind):
            goal_type = gf.body.type(
                    ContextEnvironment(Binding(gf.arg_name, type=gf.arg_type), env)
                    )

            assert isinstance(goal_type, Sort), "goal formula is not a sort."

            thm_prefix = None
            if goal_type.is_type():
                thm_prefix = '_rect'
            elif goal_type.is_prop():
                thm_prefix = '_ind'
            elif goal_type.is_set():
                thm_prefix = '_rec'
            else:
                assert False, "unknown sort : %s" % goal_type

            mutind_name = gf.arg_type.mutind_name
            ind_index = gf.arg_type.ind_index

            # when an inductive is not the only one of a mut-inductive, we can only obtain
            # the full name of the mut-inductive, i.e. Coq.Init.Datatypes.nat
            # however, all the induction theorems are declared with the full name of the
            # corresponding inductive, in other words, we have to generate them ourselves
            ind = env.mutind(mutind_name)[0].inds[ind_index]
            ind_full_segs = mutind_name.split('.')[:-1] + [ind.name]
            ind_full_name = '.'.join(ind_full_segs)
            thm_to_apply = Const(ind_full_name + thm_prefix)

            # type of an induction theorem is usually:
            #
            #     Prop with a hole -> Proof on Constructor 0 -> Proof on Constructor 1 -> ... -> Prop to Prove
            #
            # which is we need to find.
            p_hole = Lambda(gf.arg_name, gf.arg_type, gf.body)

            subgoals = []
            for c in ind.constructors:
                # form of a subgoal is usually:
                #
                #     - P c (e.g. c = O)
                #     - forall x : S1, P (c x) (e.g. c : S1 -> S2)
                #     - ...
                ctyp = c.term().type(env)

                inner = Apply(c.term())
                subgoal = Apply(p_hole, inner)
                depth = 0
                while isinstance(ctyp, Prod):
                    if ctyp.arg_type != gf.arg_type:
                        inner.args.append(Rel(depth))
                        subgoal = Prod(ctyp.arg_name, ctyp.arg_type, subgoal)
                        depth += 1
                    else:
                        inner.args.append(Rel(depth + 1))
                        subgoal = Prod(
                                ctyp.arg_name if ctyp.arg_name is not None else 'x',
                                ctyp.arg_type,
                                Prod(None, Apply(p_hole, Rel(0)), subgoal)
                                )
                        depth += 2

                    ctyp = ctyp.body

                subgoals.append(Goal(subgoal, env))

            proof = Proof(
                    Apply(thm_to_apply, p_hole, *(map(lambda g: g.formula(), subgoals))),
                    *subgoals
                    )

            print(proof.proof_formula)
            return proof
        else:
            raise cls.TacticFailure
