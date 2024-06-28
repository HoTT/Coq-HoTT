Require Import Classes.interfaces.canonical_names.
Require Import Algebra.AbGroups.
Require Import Algebra.Rings.CRing.
Require Import Spaces.Int Spaces.Pos.
Require Import WildCat.Core.

(** In this file we define the ring Z of integers. The underlying abelian group is already defined in Algebra.AbGroups.Z. Many of the ring axioms are proven and made opaque. Typically, everything inside IsCRing can be opaque since we will only ever rewrite along them and they are hprops. This also means we don't have to be too careful with how our proofs are structured. This allows us to freely use tactics such as rewrite. It would perhaps be possible to shorten many of the proofs here, but it would probably be unneeded due to the opacicty. *)

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

(** Multiplication of a ring element by an integer. *)
Definition rng_int_mult (R : Ring) (z : cring_Z) : R
  := int_iter (fun x => 1 + x) z 0.

(** Preservation of + *)
Global Instance issemigrouppreserving_plus_rng_int_mult (R : Ring)
  : IsSemiGroupPreserving (Aop:=(+)) (Bop:=(+)) (rng_int_mult R).
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

Lemma rng_int_mult_neg {R} x
  : rng_int_mult R (- x) = - rng_int_mult R x.
Proof.
  snrapply (groups.preserves_negate _).
  1-6: typeclasses eauto.
  snrapply Build_IsMonoidPreserving.
  1: exact _.
  split.
Defined.

(** Preservation of * (multiplication) *)
Global Instance issemigrouppreserving_mult_rng_int_mult (R : Ring)
  : IsSemiGroupPreserving (Aop:=(.*.)) (Bop:=(.*.)) (rng_int_mult R).
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

(** This is a ring homomorphism *)
Definition rng_homo_int (R : Ring) : (cring_Z : Ring) $-> R.
Proof.
  snrapply Build_RingHomomorphism.
  1: exact (rng_int_mult R).
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
