Require Import Holboost.plugin.

Create HintDb wtf.

Definition BAG (x:Prop) : Prop := x.

Axiom bag_true: forall (x:Prop), BAG x = True.

Hint Rewrite bag_true : wtf.
Boom Print rewrite_l2r.

Goal ((forall b,  b < 0) -> BAG (forall a, a = 0)).
Proof.
    intro.
    boom autorewrite with wtf.
    auto.
Qed.
