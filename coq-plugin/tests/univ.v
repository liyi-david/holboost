Require Import Holboost.plugin.

Inductive I : Type := i1 : Type -> I.
Variable fT : Type -> Type.

Definition t := (fT I).

Boom Remote "Const('Top.t').unfold(task).check(task)".

Definition T1 := Type.
Definition T2 := Type.

Boom Print Universes.

Definition s := T1: T2.

Boom Print Universes.

Boom Remote "Cast(Const('Top.T1'), 0, Const('Top.T2')).check(task)".
