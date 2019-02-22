Require Import Holboost.plugin.

Hypothesis H: forall (a:nat), a = 0.

Create HintDb wtf.
Hint Rewrite H : wtf.

Section A.

    Variables a b c: nat.
    Goal a + b + c = 0.
    Proof.
        autorewrite with wtf.
        boom autorewrite with wtf.
        auto.
    Qed.

End A.
