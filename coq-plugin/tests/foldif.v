Require Import Holboost.plugin.

Definition f (a:bool) :=
    if a then 1 else 0.

Definition g (n:nat) :=
    match n with
    | O => 1
    | S s => s + 1
end.

Boom Print f.
