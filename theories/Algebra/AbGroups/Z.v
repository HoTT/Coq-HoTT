Require Import Basics.
Require Import Spaces.Pos.Core Spaces.Int.
Require Import Algebra.AbGroups.AbelianGroup.

Local Set Universe Minimization ToSet.

(** * The group of integers *)

(** See also Cyclic.v for a definition of the integers as the free group on one generator. *)

Local Open Scope int_scope.

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

Local Open Scope mc_scope.

(** For every group [G] and element [g : G], the map sending an integer to that power of [g] is a homomorphism. *)
Definition grp_pow_homo {G : Group} (g : G)
  : GroupHomomorphism abgroup_Z G.
Proof.
  snrapply Build_GroupHomomorphism.
  1: exact (grp_pow g).
  intros m n; apply grp_pow_int_add.
Defined.

(** The special case for an abelian group, which gives multiplication by an integer. *)
Definition abgroup_int_mult (A : AbGroup) (a : A)
  : GroupHomomorphism abgroup_Z A
  := grp_pow_homo a.
