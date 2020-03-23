Require Import Basics Types.
Require Import Spaces.Int Spaces.Pos.
Require Import Algebra.Group.
Require Import Algebra.AbelianGroup.
Require Import Algebra.CRing.
Require Import WildCat.

(** The group of integers. *)

Definition Z : AbGroup.
Proof.
  srapply (Build_AbGroup Int); repeat split.
  + (** Operation *)
    exact int_add.
  + (** Unit *)
    exact 0%int.
  + (** Negation *)
    exact int_negation.
  + (** IsHSet *)
    exact _.
  + (** Associativity *)
    exact int_add_assoc.
  + (** Left identity *)
    exact int_add_0_l.
  + (** Right identity *)
    exact int_add_0_r.
  + (** Left inverse *)
    exact int_add_negation_l.
  + (** Right inverse *)
    exact int_add_negation_r.
  + (** Commutativity *)
    exact int_add_comm.
Defined.

(** The ring of integers *)
Definition cring_Z : CRing.
Proof.
  snrapply (Build_CRing Z).
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

(** TODO: move to Pos.Spec *)
Definition pos_peano_rec (P : Type)
  : P -> (Core.Pos -> P -> P) -> Core.Pos -> P
  := pos_peano_ind (fun _ => P).

Definition pos_peano_rec_beta_pos_succ (P : Type)
  (a : P) (f : Core.Pos -> P -> P) (p : Core.Pos)
  : pos_peano_rec P a f (pos_succ p) = f p (pos_peano_rec P a f p)
  := pos_peano_ind_beta_pos_succ (fun _ => P) a f p.

(** Standard integer operations on commutative rings *)
Definition cring_int_mul {R : CRing} (z : Int) : R
  := match z with
     | neg z => pos_peano_rec R (-1) (fun n nr => -1 + nr) z
     | 0%int => 0
     | pos z => pos_peano_rec R 1 (fun n nr => 1 + nr) z
     end.

(** Preservation of + *)
Instance issemigrouppreserving_cring_int_mul_plus (R : CRing)
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
(*     rewrite  *)
Admitted.

Instance issemigrouppreserving_cring_int_mul_mult (R : CRing)
  : IsSemiGroupPreserving (Aop:=cring_mult) (Bop:=cring_mult)
      (cring_int_mul : cring_Z -> R).
Proof.
Admitted.

(** This is a ring homomorphism *)
Definition rng_homo_int (R : CRing) : cring_Z $-> R.
Proof.
  snrapply Build_CRingHomomorphism.
  1: exact cring_int_mul.
  repeat split; exact _.
Defined.

(** TODO: move to CRing *)
Definition rng_homo_plus (A B : CRing) (f : A $-> B)
  : forall x y, f (x + y) = f x + f y
  := preserves_plus.

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
    f_ap.
    
  intros [x| |x].
  
Admitted.







