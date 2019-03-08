Require Import Holboost.plugin.

Boom Profiling On.

Hypothesis H:forall p: Prop, p = True.

Create HintDb wtf.

Hint Rewrite H : wtf.

Goal forall P : Prop, P.
Proof.
    intro.
    boom autorewrite with wtf.
    auto.
Qed.
