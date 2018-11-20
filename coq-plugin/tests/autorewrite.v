Require Import Holboost.plugin.

Definition test := fun (a: nat * nat * nat) => match a with (b, _, _) => b end.

Hypothesis H:forall n: nat, n = 0.

Create HintDb wtf.

Parameters f g : forall {A:Type},  A -> A.
Hypothesis H2: forall (A:Type), forall (a:A), (f a) = (g a).


Hint Rewrite H : wtf.
Hint Rewrite (H2 nat) : wtf.

(*
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
*)
(* make it easier to debug first ....... *)
Goal (f 1) + (f 1) = (g 0) + (g 0).

    boom autorewrite with wtf.
    auto.
Qed.
