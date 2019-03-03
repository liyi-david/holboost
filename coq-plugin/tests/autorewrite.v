Require Import Holboost.plugin.

Boom Profiling On.

Definition test := fun (a: nat * nat * nat) => match a with (b, _, _) => b end.

Hypothesis H:forall n: nat, n = 0.

Create HintDb wtf.

Parameters f g : forall {A:Type},  A -> A.
Hypothesis H2: forall (A:Type), forall (a:A), (f a) = (g a).


Hint Rewrite H : wtf.
Hint Rewrite (H2 nat) : wtf.

Boom Debug On.

Goal
    (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + 
    (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + 
    (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + 
    (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + 
    (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + 
    (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + 
    (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + 
    (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + 
    (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + 
    (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1) + (f 1)
    =
    (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + 
    (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + 
    (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + 
    (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + 
    (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + 
    (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + 
    (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + 
    (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + 
    (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + 
    (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0) + (g 0).
Proof.
    Time boom autorewrite with wtf.
    reflexivity.
Qed.
