
Declare ML Module "serialize".
Declare ML Module "mutindexport".
Declare ML Module "taskexport".
Declare ML Module "holboost".

Theorem pair_eq : forall (T1 T2:Type) (a b: T1) (c d: T2) (H1: a = b) (H2: c = d), (pair a c) = (pair b d).
Proof.
  intros.
  rewrite H1, H2.
  reflexivity.
Qed.