Require Import Basics Types.
Require Import Spaces.Int.
Require Import Algebra.AbGroups.AbelianGroup.

(** The group of integers. *)

Local Open Scope int_scope.

Definition abgroup_Z : AbGroup.
Proof.
  snrapply Build_AbGroup.
  - refine (Build_Group Int int_add 0 int_negation _); repeat split.
    + exact _.
    + exact int_add_assoc.
    + exact int_add_0_r.
    + exact int_add_negation_l.
    + exact int_add_negation_r.
  - exact int_add_comm.
Defined.
