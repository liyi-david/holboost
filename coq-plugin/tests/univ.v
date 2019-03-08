Require Import Holboost.plugin.
Boom Profiling On.
Boom Refresh.
Boom ExtractConstantBody On.

Inductive I : Type := i1 : Type -> I.
Variable fT : Type -> Type.

Definition t := (fT I).

Boom Print t.
Boom Remote "Const('Top.t').unfold(__task__).check(__task__)".

Definition T1 := Type.
Definition T2 := Type.

Boom Print Universes.

Definition s := T1: T2.

Boom Print Universes.

Boom Remote "Cast(Const('Top.T1'), 0, Const('Top.T2')).check(__task__)".
