Require Import Holboost.plugin.

Definition test := fun (a: nat * nat * nat) => match a with (b, _, _) => b end.

Create HintDb wtf.

Parameters f g : forall {A:Type},  A -> A.
Hypothesis H2: forall (A:Type), forall (a:A), (f a) = (g a).


Hint Rewrite (H2 nat) : wtf.

Boom Debug On.

Goal (f 0) + (f 0) = 0 -> (g 0) + (g 0) = 0.
Proof.
    intro H3.
    boom autorewrite with wtf in *.
    assumption.
Qed.
