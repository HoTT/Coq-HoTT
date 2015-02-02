(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics.
Require Import Types.Sigma Types.Forall.
Local Open Scope path_scope.


(** * Null homotopies of maps *)
Section NullHomotopy.
Context `{Funext}.

(** Geometrically, a nullhomotopy of a map [f : X -> Y] is an extension of [f] to a map [Cone X -> Y].  One might more simply call it e.g. [Constant f], but that is a little ambiguous: it could also reasonably mean e.g. a factorisation of [f] through [ Trunc -1 X ].  (Should the unique map [0 -> Y] be constant in one way, or in [Y]-many ways?) *)

Definition NullHomotopy {X Y : Type} (f : X -> Y)
  := {y : Y & forall x:X, f x = y}.

Lemma istrunc_nullhomotopy {n : trunc_index}
  {X Y : Type} (f : X -> Y) `{IsTrunc n Y}
  : IsTrunc n (NullHomotopy f).
Proof.
  apply @trunc_sigma; auto.
  intros y. apply (@trunc_forall _).
  intros x. apply trunc_succ.
Defined.

End NullHomotopy.
