Require Import Holboost.plugin.

Definition typ {T:Type} (_:T) := T.
Polymorphic Definition ptyp {T:Type} (_:T) := T.

(* this failes under template polymorphism *)
(* Check (typeof (typeof nat)). *)

Definition Typ1 := typ Type.

