From HoTT Require Import Basics Types.
Require Import Algebra.Groups.Group.
Require Import Algebra.Groups.Subgroup.
Require Import Algebra.Groups.QuotientGroup.
Require Import Spaces.Finite.Finite.
Require Import Spaces.Nat.Core Spaces.Nat.Division.
Require Import Truncations.Core.

Local Open Scope nat_scope.
Local Open Scope mc_mult_scope.

Set Universe Minimization ToSet.

(** * Finite Groups *)

(** ** Basic Properties *)

(** The order of a group is strictly positive. *)
Instance lt_zero_fcard_grp (G : Group) (fin_G : Finite G) : 0 < fcard G.
Proof.
  pose proof (merely_equiv_fin G) as f.
  strip_truncations.
  destruct (fcard G).
  - contradiction (f mon_unit).
  - exact _.
Defined.

(** ** Lagrange's theorem *)

(** Lagrange's Theorem - Given a finite group [G] and a finite subgroup [H] of [G], the order of [H] divides the order of [G].

Note that constructively, a subgroup of a finite group cannot be shown to be finite without excluded middle. We therefore have to assume it is. This in turn implies that the subgroup is decidable. *)
Definition divides_fcard_subgroup {U : Univalence}
  (G : Group) (H : Subgroup G) {fin_G : Finite G} {fin_H : Finite H}
  : (fcard H | fcard G).
Proof.
  exists (subgroup_index G H).
  symmetry.
  refine (fcard_quotient (in_cosetL H) @ _).
  refine (_ @ finadd_const _ _).
  apply ap, path_forall.
  srapply Quotient_ind_hprop; simpl.
  intros x.
  apply fcard_equiv'.
  apply equiv_sigma_in_cosetL_subgroup.
Defined.

(** As a corollary, the index of a subgroup is the order of the group divided by the order of the subgroup. *)
Definition subgroup_index_fcard_div {U : Univalence}
  (G : Group) (H : Subgroup G) (fin_G : Finite G) (fin_H : Finite H)
  : subgroup_index G H = fcard G / fcard H.
Proof.
  rapply nat_div_moveL_nV.
  apply divides_fcard_subgroup.
Defined.

(** Therefore we can show that the order of the quotient group [G / H] is the order of [G] divided by the order of [H]. *)
Definition fcard_grp_quotient {U : Univalence}
  (G : Group) (H : NormalSubgroup G)
  (fin_G : Finite G) (fin_H : Finite H)
  : fcard (QuotientGroup G H) = fcard G / fcard H.
Proof.
  rapply subgroup_index_fcard_div.
Defined.
