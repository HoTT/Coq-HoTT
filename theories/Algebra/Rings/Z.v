Require Import Basics Types.
Require Import Spaces.Int Spaces.Pos.
Require Import Algebra.AbGroups.
Require Import Algebra.Rings.CRing.
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
Definition cring_int_mul {R : CRing} (z : Int) : R
  := match z with
     | neg z => pos_peano_rec R (-1) (fun n nr => -1 + nr) z
     | 0%int => 0
     | pos z => pos_peano_rec R 1 (fun n nr => 1 + nr) z
     end.

(** TODO: clean up *)
(** Preservation of + *)
Global Instance issemigrouppreserving_cring_int_mul_plus (R : CRing)
  : IsSemiGroupPreserving (Aop:=cring_plus) (Bop:=cring_plus)
      (cring_int_mul : cring_Z -> R).
Proof.
  (** Unfortunately, due to how we have defined things we need to seperate this out into 9 cases. *)
  hnf. intros [x| |x] [y| |y].
  (** Some of these cases are easy however *)
  2,5,8: cbn; by rewrite right_identity.
  3,4: symmetry; apply left_identity.
  (** This leaves us with four cases to consider *)
  - cbn.
    induction y as [|y IHy] using pos_peano_ind.
    { cbn.
      rewrite pos_add_1_r.
      rewrite pos_peano_rec_beta_pos_succ.
      apply commutativity. }
    rewrite pos_add_succ_r.
    rewrite 2 pos_peano_rec_beta_pos_succ.
    rewrite simple_associativity.
    rewrite (commutativity _ (-1)).
    rewrite <- simple_associativity.
    f_ap.
  - cbn.
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
    apply right_identity.
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
Defined.

(** Preservation of * *)
Global Instance issemigrouppreserving_cring_int_mul_mult (R : CRing)
  : IsSemiGroupPreserving (Aop:=cring_mult) (Bop:=cring_mult)
      (cring_int_mul : cring_Z -> R).
Proof.
  hnf. intros [x| |x] [y| |y].
  2,5,8: symmetry; apply rng_mult_zero_r.
  3,4: cbn; symmetry; rewrite (commutativity 0); apply rng_mult_zero_r.
  { simpl.
    revert y.
    induction x as [|x IHx] using pos_peano_ind; intro y.
    { cbn.
      induction y as [|y IHy] using pos_peano_ind.
      { refine (_^ @ negate_mult (-1)).
        apply involutive. }
      rewrite 2 pos_peano_rec_beta_pos_succ.
      rewrite IHy.
      rewrite (simple_distribute_l (-1)).
      f_ap.
      refine (_^ @ negate_mult (-1)).
      apply involutive. }
    
Admitted.

(** This is a ring homomorphism *)
Definition rng_homo_int (R : CRing) : cring_Z $-> R.
Proof.
  snrapply Build_CRingHomomorphism.
  1: exact cring_int_mul.
  repeat split; exact _.
Defined.

(** The integers are the initial commutative ring *)
Global Instance isinitial_cring_Z : IsInitial cring_Z.
Proof.
  unfold IsInitial.
  intro R.
  exists (rng_homo_int R).
  intros g x.
  induction x as [x IHx| |x IHx] using int_peano_ind.
  + unfold int_pred.
    rewrite 2 rng_homo_plus.
    rewrite IHx.
    by rewrite 2 rng_homo_minus_one.
  + by rewrite 2 rng_homo_zero.
  + unfold int_succ.
    rewrite 2 rng_homo_plus.
    rewrite IHx.
    by rewrite rng_homo_one.
Defined.
