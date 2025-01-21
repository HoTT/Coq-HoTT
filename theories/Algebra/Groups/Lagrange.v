Require Import Basics Types.
Require Import Algebra.Groups.Group.
Require Import Algebra.Groups.Subgroup.
Require Import Algebra.Groups.QuotientGroup.
Require Import Spaces.Finite.Finite.
Require Import Spaces.Nat.Core Spaces.Nat.Division.
Require Import Truncations.Core.

(** ** Lagrange's theorem *)

Local Open Scope mc_mult_scope.
Local Open Scope nat_scope.

(** TODO: move to file about finite groups *)
(** The order of a group is strictly positive. *)
Global Instance lt_zero_fcard_grp (G : Group) (fin_G : Finite G) : 0 < fcard G.
Proof.
  pose proof (merely_equiv_fin G) as f.
  strip_truncations.
  destruct (fcard G).
  - contradiction (f mon_unit).
  - exact _.
Defined.

(** TODO: move to file about finite groups *)
Definition subgroup_index {U : Univalence} (G : Group) (H : Subgroup G)
  (fin_G : Finite G) (fin_H : Finite H)
  : nat.
Proof.
  refine (fcard (Quotient (in_cosetL H))).
  nrapply finite_quotient.
  1-5: exact _.
  intros x y.
  pose (dec_H := detachable_finite_subset H).
  apply dec_H.
Defined.

(** Lagrange's Theorem - Given a finite group [G] and a finite subgroup [H] of [G], the order of [H] divides the order of [G].

Note that constructively, a subgroup of a finite group cannot be shown to be finite without excluded middle. We therefore have to assume it is. This in turn implies that the subgroup is decidable. *)
Definition divides_fcard_subgroup {U : Univalence} (G : Group) (H : Subgroup G)
  (fin_G : Finite G) (fin_H : Finite H)
  : (fcard H | fcard G).
Proof.
  exists (subgroup_index G H _ _).
  symmetry.
  refine (fcard_quotient (in_cosetL H) @ _).
  refine (_ @ finadd_const _ _).
  apply ap, path_forall.
  srapply Quotient_ind_hprop.
  simpl. (** simpl is better than cbn here *)
  intros x.
  apply fcard_equiv'.
  (** Now we must show that cosets are all equivalent as types. *)
  simpl.
  snrapply equiv_functor_sigma.
  2: apply (isequiv_group_left_op x^).
  1: hnf; trivial.
  exact _.
Defined.

(** As a corollary, we can show that the order of the quotient group [G/H] is the order of [G] divided by the order of [H]. *)
Definition fcard_grp_quotient {U : Univalence} (G : Group) (H : NormalSubgroup G)
  (fin_G : Finite G) (fin_H : Finite H)
  : fcard (QuotientGroup G H) = fcard G / fcard H.
Proof.
  rapply nat_div_moveR_nV.
  apply divides_fcard_subgroup.
Defined.
