Require Import Basics Types.
Require Import Algebra.Groups.Group.
Require Import Algebra.Groups.Subgroup.
Require Import Algebra.Groups.QuotientGroup.
Require Import Spaces.Finite.
Require Import Spaces.Nat.
Require Import Colimits.Quotient.

(** ** Lagrange's theorem *)

Local Open Scope nat_scope.

Definition subgroup_index {U : Univalence} (G : Group) (H : Subgroup G)
  (fin_G : Finite G) (fin_H : Finite H)
  : nat.
Proof.
  refine (fcard (Quotient (in_cosetL H))).
  nrapply finite_quotient.
  1-6: exact _.
  intros x y.
  pose (dec_H := detachable_finite_subset H).
  apply dec_H.
Defined.

(** Given a finite group G and a finite subgroup H of G, the order of H divides the order G. Note that constructively, a subgroup of a finite group cannot be shown to be finite without exlcluded middle. We therefore have to assume it is. This in turn implies that the subgroup is decidable. *)
Theorem lagrange {U : Univalence} (G : Group) (H : Subgroup G)
  (fin_G : Finite G) (fin_H : Finite H)
  : exists d, d * (fcard H) = fcard G.
Proof.
  exists (subgroup_index G H _ _).
  symmetry.
  refine (fcard_quotient (in_cosetL H) @ _).
  refine (_ @ finplus_const _ _).
  apply ap, path_forall.
  srapply Quotient_ind_hprop.
  simpl. (** simpl is better than cbn here *)
  intros x.
  apply fcard_equiv'.
  (** Now we must show that cosets are all equivalent as types. *)
  simpl.
  snrapply equiv_functor_sigma.
  2: apply (isequiv_group_left_op (-x)).
  1: hnf; trivial.
  exact _.
Defined.

Corollary lagrange_noraml {U : Univalence} (G : Group) (H : NormalSubgroup G)
  (fin_G : Finite G) (fin_H : Finite H)
  : fcard (QuotientGroup G H) * fcard H = fcard G.
Proof.
  apply lagrange.
Defined.
