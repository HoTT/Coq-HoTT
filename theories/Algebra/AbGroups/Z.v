From HoTT Require Import Basics.
Require Import Spaces.Pos.Core Spaces.Int.
Require Import Algebra.AbGroups.AbelianGroup.

Local Set Universe Minimization ToSet.

Local Open Scope int_scope.
Local Open Scope mc_add_scope.

(** * The group of integers *)

(** See also Cyclic.v for a definition of the integers as the free group on one generator. *)

Definition abgroup_Z@{} : AbGroup@{Set}.
Proof.
  snapply Build_AbGroup'.
  - exact Int.
  - exact 0%int.
  - exact int_neg.
  - exact int_add.
  - exact _.
  - exact int_add_comm.
  - exact int_add_assoc.
  - exact int_add_0_l.
  - exact int_add_neg_l.
Defined.

(** For every group [G] and element [g : G], the map sending an integer to that power of [g] is a homomorphism.  See [ab_mul] for the homomorphism [G -> G] when [G] is abelian. *)
Definition grp_pow_homo {G : Group} (g : G)
  : GroupHomomorphism abgroup_Z G.
Proof.
  snapply Build_GroupHomomorphism.
  1: exact (grp_pow g).
  intros m n; apply grp_pow_add.
Defined.

(** [ab_mul] (and [grp_pow]) give multiplication in [abgroup_Z]. *)
Definition abgroup_Z_ab_mul (z z' : Int)
  : ab_mul (A:=abgroup_Z) z z' = z * z'.
Proof.
  revert z.
  rapply (int_homotopic (fun x => int_add x z')); cbn beta.
  1,3: reflexivity.
  - intro z.
    lhs napply (grp_pow_succ (G:=abgroup_Z)).
    by rewrite int_add_comm.
Defined.
