Require Import Holboost.plugin.

Definition typ {T:Type} (_:T) := T.
Polymorphic Definition ptyp {T:Type} (_:T) := T.

(* this failes under template polymorphism *)
(* Check (typeof (typeof nat)). *)

Definition Typ1 := typ Type.

Boom Debug On.

Definition T1 := Type.
Definition T2 := Type.

Boom Print Universes.
