Require Import Basics.
Require Import Spaces.Pos.Core Spaces.BinInt.
Require Import Algebra.AbGroups.AbelianGroup.

Local Set Universe Minimization ToSet.

(** * The group of integers *)

(** See also Cyclic.v for a definition of the integers as the free group on one generator. *)

Local Open Scope binint_scope.

(** TODO: switch to [Int] *)
Definition abgroup_Z@{} : AbGroup@{Set}.
Proof.
  snrapply Build_AbGroup.
  - refine (Build_Group BinInt binint_add 0 binint_negation _); repeat split.
    + exact _.
    + exact binint_add_assoc.
    + exact binint_add_0_r.
    + exact binint_add_negation_l.
    + exact binint_add_negation_r.
  - exact binint_add_comm.
Defined.
