Require Import Holboost.plugin.

Inductive S : Type -> Type := s : Type -> (S nat).

(*
clearly type of S is Type@{...} -> Type@{...}
but when we check S, we get Type@{Set+1}
*)
Boom Check S.
