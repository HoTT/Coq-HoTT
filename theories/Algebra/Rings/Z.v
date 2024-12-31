Require Import Classes.interfaces.canonical_names.
Require Import Algebra.AbGroups.
Require Import Algebra.Rings.CRing.
Require Import Spaces.Int Spaces.Pos.
Require Import WildCat.Core.

(** * In this file we define the ring [cring_Z] of integers with underlying abelian group [abgroup_Z] defined in Algebra.AbGroups.Z. We also define multiplication by an integer in a general ring, and show that [cring_Z] is initial. *)

(** The ring of integers *)
Definition cring_Z : CRing.
Proof.
  snrapply Build_CRing'.
  - exact abgroup_Z.
  - exact 1%int.
  - exact int_mul.
  - exact int_mul_comm.
  - exact int_mul_assoc.
  - exact int_dist_l.
  - exact int_mul_1_l.
Defined.

Local Open Scope mc_scope.

(** Given a ring element [r], we get a map [Int -> R] sending an integer to that multiple of [r]. *)
Definition rng_int_mult (R : Ring) := grp_pow_homo : R -> Int -> R.

(** Multiplying a ring element [r] by an integer [n] is equivalent to first multiplying the unit [1] of the ring by [n], and then multiplying the result by [r].  This is distributivity of right multiplication by [r] over the sum. *)
Definition rng_int_mult_dist_r {R : Ring} (r : R) (n : cring_Z)
  : rng_int_mult R r n = (rng_int_mult R 1 n) * r.
Proof.
  cbn.
  rhs nrapply (grp_pow_natural (grp_homo_rng_right_mult r)); cbn.
  by rewrite rng_mult_one_l.
Defined.

(** Similarly, there is a left-distributive law. *)
Definition rng_int_mult_dist_l {R : Ring} (r : R) (n : cring_Z)
  : rng_int_mult R r n = r * (rng_int_mult R 1 n).
Proof.
  cbn.
  rhs nrapply (grp_pow_natural (grp_homo_rng_left_mult r)); cbn.
  by rewrite rng_mult_one_r.
Defined.

(** [rng_int_mult R 1] preserves multiplication.  This requires that the specified ring element is the unit. *)
Global Instance issemigrouppreserving_mult_rng_int_mult (R : Ring)
  : IsSemiGroupPreserving (A:=cring_Z) (Aop:=(.*.)) (Bop:=(.*.)) (rng_int_mult R 1).
Proof.
  intros x y.
  cbn; unfold sg_op.
  lhs nrapply grp_pow_int_mul.
  nrapply rng_int_mult_dist_l.
Defined.

(** [rng_int_mult R 1] is a ring homomorphism *)
Definition rng_homo_int (R : Ring) : (cring_Z : Ring) $-> R.
Proof.
  snrapply Build_RingHomomorphism.
  1: exact (rng_int_mult R 1).
  repeat split.
  1,2: exact _.
  apply rng_plus_zero_r.
Defined.

(** The integers are the initial commutative ring *)
Global Instance isinitial_cring_Z : IsInitial cring_Z.
Proof.
  unfold IsInitial.
  intro R.
  exists (rng_homo_int R).
  intros g x.
  unfold rng_homo_int, rng_int_mult; cbn.
  induction x as [|x|x].
  - by rhs nrapply (grp_homo_unit g).
  - rewrite grp_pow_succ.
    change (x.+1%int) with (1 + x)%int.
    rewrite (rng_homo_plus g 1 x).
    rewrite rng_homo_one.
    f_ap.
  - rewrite grp_pow_pred.
    rewrite IHx.
    clear IHx.
    change (-1 + g (-x)%int = g (-x).-1%int).
    rewrite <- (rng_homo_minus_one g).
    lhs_V nrapply (rng_homo_plus g).
    f_ap.
Defined.
