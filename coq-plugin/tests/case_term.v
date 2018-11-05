Require Import Holboost.plugin.

Definition f (n:nat) :=
    match n with
    | O => 1
    | S (S m) => 2 + m
    | S _ => 0
end.
