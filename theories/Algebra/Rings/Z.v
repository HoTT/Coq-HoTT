Require Import Classes.interfaces.canonical_names.
Require Import Algebra.AbGroups.
Require Import Algebra.Rings.CRing.
Require Import Spaces.Int Spaces.Pos.
Require Import WildCat.Core.

(** * In this file we define the ring [cring_Z] of integers with underlying abelian group [abroup_Z] defined in Algebra.AbGroups.Z. We also define multiplication by an integer in a general ring, and show that [cring_Z] is initial. *)

(** The ring of integers *)
Definition cring_Z : CRing.
Proof.
  snrapply Build_CRing'.
  6: repeat split.
  - exact abgroup_Z.
  - exact 1%int.
  - exact int_mul.
  - exact int_mul_comm.
  - exact int_dist_l.
  - exact _.
  - exact int_mul_assoc.
  - exact int_mul_1_l.
  - exact int_mul_1_r.
Defined.

Local Open Scope mc_scope.

(** Every ring element can be multiplied by an integer. *)
Definition rng_int_mult (R : Ring) (r : R) (z : cring_Z) : R
  := int_iter (fun x => r + x) z 0.

(** [rng_int_mult R r] preserves addition. *)
Global Instance issemigrouppreserving_plus_rng_int_mult (R : Ring) (r : R)
  : IsSemiGroupPreserving (Aop:=(+)) (Bop:=(+)) (rng_int_mult R r).
Proof.
  intros x y.
  induction x as [|x|x].
  - simpl.
    rhs nrapply left_identity.
    2: exact _.
    reflexivity.
  - cbn.
    rewrite int_add_succ_l.
    unfold rng_int_mult.
    rewrite 2 int_iter_succ_l.
    rhs_V nrapply simple_associativity.
    2: exact _.
    f_ap.
  - cbn.
    rewrite int_add_pred_l.
    unfold rng_int_mult.
    rewrite 2 int_iter_pred_l.
    rhs_V nrapply simple_associativity.
    2: exact _.
    f_ap.
Defined.

(** [rng_int_mult R r] sends [0 : Int] to [0 : R] definitionally. *)
Global Instance isunitpreserving_plus_rng_int_mult (R : Ring) (r : R)
  : IsUnitPreserving (Aunit:=zero) (Bunit:=canonical_names.zero) (rng_int_mult R r)
  := idpath.

(** [rng_int_mult R r] preserves addition and zero. *)
Global Instance ismonoidpreserving_plus_rng_int_mult (R : Ring) (r : R)
  : IsMonoidPreserving (Aop:=(+)) (Bop:=(+)) (rng_int_mult R r)
  := {}.

(** [rng_int_mult R r] commutes with negation. *)
Lemma rng_int_mult_neg (R : Ring) (r : R) x
  : rng_int_mult R r (- x) = - rng_int_mult R r x.
Proof.
  snrapply (groups.preserves_negate _); exact _.
Defined.

(** [rng_int_mult R 1] preserves multiplication.  This requires that the specified ring element is the unit. *)
Global Instance issemigrouppreserving_mult_rng_int_mult (R : Ring)
  : IsSemiGroupPreserving (Aop:=(.*.)) (Bop:=(.*.)) (rng_int_mult R 1).
Proof.
  intros x y.
  induction x as [|x|x].
  - simpl.
    by rhs nrapply rng_mult_zero_l.
  - cbn.
    rewrite int_mul_succ_l.
    rewrite issemigrouppreserving_plus_rng_int_mult.
    unfold rng_int_mult in *.
    rewrite int_iter_succ_l.
    rhs nrapply rng_dist_r.
    rewrite rng_mult_one_l.
    rewrite IHx.
    reflexivity.
  - cbn.
    rewrite int_mul_pred_l.
    rewrite issemigrouppreserving_plus_rng_int_mult.
    unfold rng_int_mult in *.
    rewrite int_iter_pred_l.
    rhs nrapply rng_dist_r.
    rewrite IHx.
    f_ap.
    lhs rapply rng_int_mult_neg.
    symmetry; apply rng_mult_negate.
Defined.

(** [rng_int_mult R 1] is a ring homomorphism *)
Definition rng_homo_int (R : Ring) : (cring_Z : Ring) $-> R.
Proof.
  snrapply Build_RingHomomorphism.
  1: exact (rng_int_mult R 1).
  repeat split.
  1,2: exact _.
  hnf.
  apply rng_plus_zero_r.
Defined.

(** The integers are the initial commutative ring *)
Global Instance isinitial_cring_Z : IsInitial cring_Z.
Proof.
  unfold IsInitial.
  intro R.
  exists (rng_homo_int R).
  intros g x.
  induction x as [|x|x].
  - by rhs nrapply (grp_homo_unit g).
  - unfold rng_homo_int, rng_int_mult; cbn.
    rewrite int_iter_succ_l.
    change (x.+1%int) with (1 + x)%int.
    rewrite (rng_homo_plus g 1 x).
    rewrite rng_homo_one.
    f_ap.
  - unfold rng_homo_int, rng_int_mult in IHx |- *; cbn in IHx |- *.
    rewrite int_iter_pred_l.
    cbn.
    rewrite IHx.
    clear IHx.
    rewrite <- (rng_homo_one g).
    rewrite <- (rng_homo_negate g).
    lhs_V nrapply (rng_homo_plus g).
    f_ap.
Defined.
