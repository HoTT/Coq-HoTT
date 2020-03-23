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

(** Standard integer operations on commutative rings *)
Definition cring_int_mul {R : CRing} (z : Int) : R
  := match z with
     | neg z => pos_peano_rec R (-1) (fun n nr => -1 + nr) z
     | 0%int => 0
     | pos z => pos_peano_rec R 1 (fun n nr => 1 + nr) z
     end.

(** Importantly this is a ring homomorphism *)
Definition rng_homo_int (R : CRing) : cring_Z $-> R.
Proof.
  snrapply Build_CRingHomomorphism.
  1: exact cring_int_mul.
  (** To show that this map preserves both monoids we only need to show it preserves both operations. Typeclasses can deduce this for us. *)
  repeat split.
  + (** Preservation of + *)
    (** Unfortunately, due to how we have defined things we need to seperate this out into 9 cases. *)
    hnf. intros [x| |x] [y| |y].
    (** Some of these cases are easy however *)
    2,5,8: cbn; by rewrite right_identity.
    3,4: symmetry; apply left_identity.
    (** This leaves us with four cases to consider *)
    - cbn.
      destruct y.
      * cbn.
Admitted.



(** The integers are the initial commutative ring *)
Global Instance isinitial_cring_Z : IsInitial cring_Z.
Proof.
  unfold IsInitial.
  intro X.
  snrefine (_;_).
  {(** This is tricky *)
Admitted.
