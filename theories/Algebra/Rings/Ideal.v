Require Import Basics Types.
Require Import Algebra.Rings.CRing.
Require Import Algebra.AbGroups.

Local Open Scope mc_scope.

(** In this file we define Ideals *)

(** TODO: In the future it might be useful to define ideals as submodules when we go about defining R-modules. *)

(** An additive subgroup I of a ring R is an ideal when: *)
Class IsIdeal {R : CRing} (I : Subgroup R) :=
  isideal (r x : R) : I x -> I (r * x).

Record Ideal (R : CRing) := {
  ideal_subgroup : Subgroup R;
  ideal_isideal : IsIdeal ideal_subgroup;
}.

Coercion ideal_subgroup : Ideal >-> Subgroup.
Global Existing Instances ideal_isideal.

Section Examples.

  Context (R : CRing).

  (** The zero ideal is an ideal *)
  Global Instance isideal_trivial_subgroup
    : IsIdeal (R:=R) trivial_subgroup.
  Proof.
    hnf; cbn. intros r x p.
    refine (_ @ rng_mult_zero_r r).
    f_ap.
  Defined.

  (** Zero ideal *)
  Definition ideal_zero : Ideal R
    := Build_Ideal R _ isideal_trivial_subgroup.

  (** The unit ideal is an ideal *)
  Global Instance isideal_maximal_subgroup
    : IsIdeal (R:=R) maximal_subgroup.
  Proof.
    split.
  Defined.

  (** Unit ideal *)
  Definition ideal_unit : Ideal R
    := Build_Ideal R _ isideal_maximal_subgroup.

(** TODO: Intersection of ideals *)
(** TODO: Sum of ideals *)
(** TODO: Product of ideals *)

End Examples.

Definition ideal_kernel {R S : CRing} (f : CRingHomomorphism R S) : Ideal R.
Proof.
  snrapply Build_Ideal.
  1: exact (grp_kernel f).
  intros r x p; cbn in p.
  simpl.
  refine (rng_homo_mult _ _ _ @ _).
  refine (_ @ rng_mult_zero_r (f r)).
  f_ap.
Defined.

(** Properties of ideals *)

(** TODO: Maximal ideals *)
(** TODO: Principal ideal *)
(** TODO: Prime ideals *)
(** TODO: Radical ideals *)
(** TODO: Minimal ideals *)
(** TODO: Primary ideals *)

