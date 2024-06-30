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

Definition rng_int_mult (R : Ring) := abgroup_int_mult R. 

(** [rng_int_mult R 1] preserves multiplication.  This requires that the specified ring element is the unit. *)
Global Instance issemigrouppreserving_mult_rng_int_mult (R : Ring)
  : IsSemiGroupPreserving (A:=cring_Z) (Aop:=(.*.)) (Bop:=(.*.)) (rng_int_mult R 1).
Proof.
  intros x y.
  induction x as [|x|x].
  - simpl.
    by rhs nrapply rng_mult_zero_l.
  - cbn.
    rewrite int_mul_succ_l.
    unfold rng_int_mult in *.
    rewrite issemigrouppreserving_plus_abgroup_int_mult.
    unfold abgroup_int_mult in *.
    rewrite grp_pow_int_add_1.
    rhs nrapply rng_dist_r.
    rewrite rng_mult_one_l.
    rewrite IHx.
    reflexivity.
  - cbn.
    rewrite int_mul_pred_l.
    unfold rng_int_mult in *.
    rewrite issemigrouppreserving_plus_abgroup_int_mult.
    unfold abgroup_int_mult in *.
    rewrite grp_pow_int_sub_1.
    rhs nrapply rng_dist_r.
    rewrite IHx.
    f_ap.
    lhs rapply abgroup_int_mult_neg.
    symmetry; apply rng_mult_negate.
Defined.

(** [rng_int_mult R 1] is a ring homomorphism *)
Definition rng_homo_int (R : Ring) : (cring_Z : Ring) $-> R.
Proof.
  snrapply Build_RingHomomorphism.
  1: exact (rng_int_mult R 1).
  repeat split.
  1,2: exact _.
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
    unfold abgroup_int_mult.
    rewrite grp_pow_int_add_1.
    change (x.+1%int) with (1 + x)%int.
    rewrite (rng_homo_plus g 1 x).
    rewrite rng_homo_one.
    f_ap.
  - unfold rng_homo_int, rng_int_mult in IHx |- *; cbn in IHx |- *.
    unfold abgroup_int_mult in *.
    rewrite grp_pow_int_sub_1.
    cbn.
    rewrite IHx.
    clear IHx.
    rewrite <- (rng_homo_one g).
    rewrite <- (rng_homo_negate g).
    lhs_V nrapply (rng_homo_plus g).
    f_ap.
Defined.
