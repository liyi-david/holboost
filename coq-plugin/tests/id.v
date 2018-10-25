Require Import Holboost.plugin.

Definition id {T:Type} (t:T) := t.

Polymorphic Definition pid {T:Type} (t:T) := t.

Definition f (t:Type) := prod nat t.

Definition g := f nat.
