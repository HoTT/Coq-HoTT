(* -*- mode: coq; mode: visual-line -*- *)

Require Import HoTT.Basics HoTT.Types.

Local Open Scope path_scope.
Generalizable Variables A B f.

(** * Bi-invertible maps *)

(** A map is "bi-invertible" if it has both a section and a retraction, not necessarily the same.  This definition of equivalence was proposed by Andre Joyal. *)

Definition BiInv `(f : A -> B) : Type
  := {g : B -> A & g o f == idmap} * {h : B -> A & f o h == idmap}.

(** It seems that the easiest way to show that bi-invertibility is equivalent to being an equivalence is also to show that both are h-props and that they are logically equivalent. *)

Definition isequiv_biinv `(f : A -> B)
  : BiInv f -> IsEquiv f.
Proof.
  intros [[g s] [h r]].
  exact (isequiv_adjointify f g
    (fun x => ap f (ap g (r x)^ @ s (h x))  @ r x)
    s).
Defined.

Global Instance isprop_biinv `{Funext} `(f : A -> B) : IsHProp (BiInv f) | 0.
Proof.
  apply hprop_inhabited_contr.
  intros bif; pose (fe := isequiv_biinv f bif).
  apply @contr_prod.
  (* For this, we've done all the work already. *)
  - by apply contr_retr_equiv.
  - by apply contr_sect_equiv.
Defined.

Definition equiv_biinv_isequiv `{Funext} `(f : A -> B)
  : BiInv f <~> IsEquiv f.
Proof.
  apply equiv_iff_hprop.
  - by apply isequiv_biinv.
  - intros ?.  split.
    + by exists (f^-1); apply eissect.
    + by exists (f^-1); apply eisretr.
Defined.
