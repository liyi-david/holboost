Require Import Holboost.plugin.

Hypothesis H: forall (a:nat), a = 0.

Create HintDb wtf.

Section A.

    Variables a b c: nat.

    Hint Rewrite (H a): wtf.
    Hint Rewrite (H b): wtf.
    Hint Rewrite (H c): wtf.

    Goal a + a + b + c = 0.
    Proof.
        autorewrite with wtf.
        auto.
    Qed.

End A.
