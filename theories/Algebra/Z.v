Require Import Basics.
Require Import Types.
Require Import Spaces.Int.
Require Import Algebra.Group.
Require Import Algebra.AbelianGroup.
Require Import Algebra.CRing.

(** The group of integers. *)

Local Open Scope int_scope.

Definition abgroup_Z : AbGroup.
Proof.
  srapply (Build_AbGroup Int); repeat split.
  + (** Operation *)
    exact int_add.
  + (** Unit *)
    exact 0.
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

Notation Z := abgroup_Z.

(** The ring of integers *)

Definition cring_Z : CRing.
Proof.
  snrapply (Build_CRing abgroup_Z).
  6: split; [exact _ | repeat split | ].
  + (** Multiplication *)
    exact int_mul.
  + (** Multiplicative unit *)
    exact 1.
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
