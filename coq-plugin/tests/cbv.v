Require Import Holboost.plugin.

Definition f := 0.
Definition f1 := 0.
Definition f2 := 0.
Definition f3 := 0.
Definition f4 := 0.

Goal f + f1 + f2 + f3 + f4 = 0.
Proof.
    boom cbv "Top\.f".
    reflexivity.
Qed.
