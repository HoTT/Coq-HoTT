Require Import Basics.
Require Import Spaces.Pos.Core Spaces.Int.
Require Import Algebra.AbGroups.AbelianGroup.

Local Set Universe Minimization ToSet.

(** * The group of integers *)

(** See also Cyclic.v for a definition of the integers as the free group on one generator. *)

Local Open Scope int_scope.

(** TODO: switch to [Int] *)
Definition abgroup_Z@{} : AbGroup@{Set}.
Proof.
  snrapply Build_AbGroup.
  - refine (Build_Group Int int_add 0 int_neg _); repeat split.
    + exact _.
    + exact int_add_assoc.
    + exact int_add_0_r.
    + exact int_add_neg_l.
    + exact int_add_neg_r.
  - exact int_add_comm.
Defined.
