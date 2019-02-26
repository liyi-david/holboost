Declare ML Module "hbcommon".
Declare ML Module "hbprofile".
Declare ML Module "hbtactics".
Declare ML Module "declbuf".
Declare ML Module "debug".
Declare ML Module "univexport".
Declare ML Module "serialize".
Declare ML Module "hbsync".
Declare ML Module "mutindexport".
Declare ML Module "taskexport".
Declare ML Module "boom_autorewrite".
Declare ML Module "holboost".

Theorem pair_eq : forall (T1 T2:Type) (a b: T1) (c d: T2) (H1: a = b) (H2: c = d), (pair a c) = (pair b d).
Proof.
  intros.
  rewrite H1, H2.
  reflexivity.
Qed.

(* we use`` the following theorem to rewrite b with a while a = b *)
Theorem rewrite_l2r : forall (T:Type) (a b:T) (P: T -> Prop), a = b -> (P b -> P a).
Proof.
  intros T a b P H.
  rewrite H.
  intro H1.
  apply H1.
Qed.

Theorem rewrite_r2l : forall (T:Type) (a b:T) (P: T -> Prop), a = b -> (P a -> P b).
Proof.
  intros T a b P H.
  rewrite <-H.
  intro H1.
  apply H1.
Qed.
