Require Import Holboost.plugin.

Boom Profiling On.

Hypothesis H : 1 = 0.

Create HintDb wtf.

Hint Rewrite H : wtf.

Boom Debug On.

Goal 1000 = 0 -> 999 = 0.
Proof.
    intro.
    boom autorewrite with wtf in *.
    assumption.
Qed.
