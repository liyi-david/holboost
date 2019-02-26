Require Import Holboost.plugin.

Open Scope type_scope.

Create HintDb wtf.

Variable f: forall (B:Type)(A:Type)(lst: A * A), B.
Hypothesis H: forall (A:Type) (lst: A * A), f nat A lst = 0.

Hint Rewrite H : wtf.

Goal forall (A1 A2:Type) (lst1: A1 * A1) (lst2: A2 * A2), f nat A1 lst1 = f nat A2 lst2.
Proof.
    intros.
(*
    apply (rewrite_l2r (nat * nat)
    (f nat A1 lst1, f nat A2 lst2)
    (0, 0)
    (fun __VAR_TUPLE : nat * nat =>
        fst __VAR_TUPLE = snd __VAR_TUPLE)
        (pair_eq nat nat
        (f nat A1 lst1) 0
        (f nat A2 lst2) 0
        (H A1 lst1)
        (H A2 lst2))).
*)
    Boom Print Universes.
    boom autorewrite with wtf.
    auto.
Qed.
