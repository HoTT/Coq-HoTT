From HoTT Require Import Basics Types.Prod Types.Equiv.

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
    (fun x => ap f (ap g (r x)^ @ s (h x)) @ r x)
    s).
Defined.

Definition biinv_isequiv `(f : A -> B)
  : IsEquiv f -> BiInv f.
Proof.
  intros [g s r adj].
  exact ((g; r), (g; s)).
Defined.

Definition iff_biinv_isequiv `(f : A -> B)
  : BiInv f <-> IsEquiv f.
Proof.
  split.
  - apply isequiv_biinv.
  - apply biinv_isequiv.
Defined.

Instance ishprop_biinv `{Funext} `(f : A -> B) : IsHProp (BiInv f) | 0.
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
  apply equiv_iff_hprop_uncurried, iff_biinv_isequiv.
Defined.
