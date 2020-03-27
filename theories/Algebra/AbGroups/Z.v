Require Import Basics Types.
Require Import Spaces.Int.
Require Import Algebra.AbGroups.AbelianGroup.

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
