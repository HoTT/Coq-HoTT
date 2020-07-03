Require Import Basics Types.
Require Import Algebra.AbGroups.
Require Import Algebra.Rings.CRing.
Require Import Spaces.Int Spaces.Pos.
Require Import WildCat.

(** The ring of integers *)
Definition cring_Z : CRing.
Proof.
  snrapply (Build_CRing abgroup_Z).
  6: split; [exact _ | repeat split | ].
  + (** Multiplication *)
    exact int_mul.
  + (** Multiplicative unit *)
    exact 1%int.
  + (** IsHSet *)
    exact _.
  + (** Associativity of multiplication *)
    exact int_mul_assoc.
  + (** Left identity *)
    exact int_mul_1_l.
  + (** Right identity *)
    exact int_mul_1_r.
  + (** Commutativity of integer multiplication *)
    exact int_mul_comm.
  + (** Left distributivity *)
    exact int_mul_add_distr_l.
Defined.

Local Open Scope mc_scope.

(** Standard integer operations on commutative rings *)
Definition cring_int_mul (R : CRing) (z : cring_Z) : R
  := match z with
     | neg z => pos_peano_rec R (-1) (fun n nr => -1 + nr) z
     | 0%int => 0
     | pos z => pos_peano_rec R 1 (fun n nr => 1 + nr) z
     end.

(** TODO: clean up *)
(** Preservation of + *)
Global Instance issemigrouppreserving_cring_int_mul_plus (R : CRing)
  : IsSemiGroupPreserving (Aop:=cring_plus) (Bop:=cring_plus)
      (cring_int_mul R : cring_Z -> R).
Proof.
  (** Unfortunately, due to how we have defined things we need to seperate this out into 9 cases. *)
  hnf. intros [x| |x] [y| |y].
  (** Some of these cases are easy however *)
  2,5,8: cbn; by rewrite right_identity.
  3,4: symmetry; apply left_identity.
  (** This leaves us with four cases to consider *)
  (** x < 0 , y < 0 *)
  { change (cring_int_mul R ((neg x) + (neg y))%int
      = (cring_int_mul R (neg x)) + (cring_int_mul R (neg y))).
    induction y as [|y IHy] using pos_peano_ind.
    { simpl.
      rewrite pos_add_1_r.
      rewrite pos_peano_rec_beta_pos_succ.
      apply commutativity. }
    simpl.
    rewrite pos_add_succ_r.
    rewrite 2 pos_peano_rec_beta_pos_succ.
    rewrite simple_associativity.
    rewrite (commutativity _ (-1)).
    rewrite <- simple_associativity.
    f_ap. }
  (** x < 0 , y > 0 *)
  { cbn.
    revert x.
    induction y as [|y IHy] using pos_peano_ind; intro x.
    { cbn.
      induction x as [|x] using pos_peano_ind.
      1: symmetry; cbn; apply left_inverse.
      rewrite pos_peano_rec_beta_pos_succ.
      rewrite int_pos_sub_succ_r.
      cbn; rewrite <- simple_associativity.
      apply moveL_equiv_M.
      cbn; rewrite involutive.
      apply commutativity. }
    induction x as [|x IHx] using pos_peano_ind.
    { rewrite int_pos_sub_succ_l.
      cbn; apply moveL_equiv_M.
      cbn; rewrite involutive.
      by rewrite pos_peano_rec_beta_pos_succ. }
    rewrite int_pos_sub_succ_succ.
    rewrite IHy.
    rewrite 2 pos_peano_rec_beta_pos_succ.
    rewrite (commutativity (-1)).
    rewrite simple_associativity.
    rewrite <- (simple_associativity _ _ 1).
    rewrite left_inverse.
    f_ap.
    symmetry.
    apply right_identity. }
  - cbn.
    revert x.
    induction y as [|y IHy] using pos_peano_ind; intro x.
    { induction x as [|x] using pos_peano_ind.
      1: symmetry; cbn; apply right_inverse.
      rewrite pos_peano_rec_beta_pos_succ.
      rewrite (commutativity 1).
      rewrite <- simple_associativity.
      rewrite int_pos_sub_succ_l.
      cbn; by rewrite right_inverse, right_identity. }
    induction x as [|x IHx] using pos_peano_ind.
    { rewrite int_pos_sub_succ_r.
      rewrite pos_peano_rec_beta_pos_succ.
      rewrite simple_associativity.
      cbn.
      rewrite (right_inverse 1).
      symmetry.
      apply left_identity. }
    rewrite int_pos_sub_succ_succ.
    rewrite IHy.
    rewrite 2 pos_peano_rec_beta_pos_succ.
    rewrite (commutativity 1).
    rewrite simple_associativity.
    rewrite <- (simple_associativity _ _ (-1)).
    rewrite (right_inverse 1).
    f_ap; symmetry.
    apply right_identity.
  - cbn.
    induction y as [|y IHy] using pos_peano_ind.
    { cbn.
      rewrite pos_add_1_r.
      rewrite pos_peano_rec_beta_pos_succ.
      apply commutativity. }
    rewrite pos_add_succ_r.
    rewrite 2 pos_peano_rec_beta_pos_succ.
    rewrite simple_associativity.
    rewrite IHy.
    rewrite simple_associativity.
    rewrite (commutativity 1).
    reflexivity.
Qed.

Lemma cring_int_mul_negate {R} x
  : cring_int_mul R (- x) = - cring_int_mul R x.
Proof.
  snrapply (groups.preserves_negate _).
  1-6: exact _.
  snrapply Build_IsMonoidPreserving.
  1: exact _.
  split.
Defined.

Lemma cring_int_mul_pos_mult {R} x y
  : cring_int_mul R (pos x * pos y)%int
    = cring_int_mul R (pos x) * cring_int_mul R (pos y).
Proof.
  revert y.
  induction x as [|x IHx] using pos_peano_ind; intro y.
  { symmetry.
    apply left_identity. }
  change (cring_int_mul R (pos (pos_succ x * y)%pos)
    = cring_int_mul R (pos (pos_succ x)) * cring_int_mul R (pos y)).
  rewrite pos_mul_succ_l.
  change (cring_int_mul R ((pos (x * y)%pos : cring_Z) + pos y)
    = cring_int_mul R (pos (pos_succ x)) * cring_int_mul R (pos y)).
  refine (issemigrouppreserving_cring_int_mul_plus
    R (pos (x * y)%pos) (pos y) @ _).
  change (cring_int_mul R (pos (x * y)%pos) + cring_int_mul R (pos y)
    = cring_int_mul R (pos (pos_succ x)) * cring_int_mul R (pos y)).
  rewrite IHx.
  transitivity ((1 + cring_int_mul R (pos x)) * cring_int_mul R (pos y)).
  2: simpl; by rewrite pos_peano_rec_beta_pos_succ.
  rewrite rng_dist_r.
  rewrite rng_mult_one_l.
  apply commutativity.
Qed.

(** Preservation of * *)
Global Instance issemigrouppreserving_cring_int_mul_mult (R : CRing)
  : IsSemiGroupPreserving (Aop:=cring_mult) (Bop:=cring_mult)
      (cring_int_mul R : cring_Z -> R).
Proof.
  hnf. intros [x| |x] [y| |y].
  2,5,8: symmetry; apply rng_mult_zero_r.
  3,4: cbn; symmetry; rewrite (commutativity 0); apply rng_mult_zero_r.
  { change (cring_int_mul R (pos (x * y)%pos)
      = cring_int_mul R (- (pos x : cring_Z))
        * cring_int_mul R (- (pos y : cring_Z))).
    by rewrite 2 cring_int_mul_negate, cring_int_mul_pos_mult,
      rng_mult_negate_negate. }
  { change (cring_int_mul R (- (pos (x * y)%pos : cring_Z))
      = cring_int_mul R (- (pos x : cring_Z))
        * cring_int_mul R (pos y)).
    by rewrite 2 cring_int_mul_negate, cring_int_mul_pos_mult, rng_mult_negate_l. }
  { change (cring_int_mul R (- (pos (x * y)%pos : cring_Z))
      = cring_int_mul R (pos x)
        * cring_int_mul R (- (pos y : cring_Z))).
    by rewrite 2 cring_int_mul_negate, cring_int_mul_pos_mult, rng_mult_negate_r. }
  apply cring_int_mul_pos_mult.
Qed.

(** This is a ring homomorphism *)
Definition rng_homo_int (R : CRing) : cring_Z $-> R.
Proof.
  snrapply Build_CRingHomomorphism.
  1: exact (cring_int_mul R).
  repeat split; exact _.
Defined.

(** The integers are the initial commutative ring *)
Global Instance isinitial_cring_Z : IsInitial cring_Z.
Proof.
  unfold IsInitial.
  intro R.
  exists (rng_homo_int R).
  intros g x.
  destruct x as [n| |p].
  + induction n using pos_peano_ind.
    { cbn. rapply rng_homo_minus_one. }
    simpl.
    rewrite pos_peano_rec_beta_pos_succ.
    rewrite int_neg_pos_succ.
    unfold int_pred.
    rewrite int_add_comm.
    rewrite rng_homo_plus.
    rewrite rng_homo_minus_one.
    apply ap.
    exact IHn.
  + by rewrite 2 rng_homo_zero.
  + induction p using pos_peano_ind.
    { cbn. rapply rng_homo_one. }
    simpl.
    rewrite pos_peano_rec_beta_pos_succ.
    rewrite int_pos_pos_succ.
    unfold int_succ.
    rewrite int_add_comm.
    rewrite rng_homo_plus.
    rewrite rng_homo_one.
    apply ap.
    exact IHp.
Defined.
