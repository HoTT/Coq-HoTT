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

Local Open Scope mc_scope.

(** Every element of an abelian group can be multiplied by an integer. *)
Definition abgroup_int_mult (A : AbGroup) (x : A) (z : abgroup_Z) : A
  := grp_pow x z.

(** [abgroup_int_mult A r] preserves addition. *)
Global Instance issemigrouppreserving_plus_abgroup_int_mult (A : AbGroup) (x : A)
  : IsSemiGroupPreserving (Aop:=(+)) (Bop:=(+)) (abgroup_int_mult A x).
Proof.
  intros y z.
  apply grp_pow_int_add.
Defined.

(** [abgroup_int_mult A r] sends [0 : Int] to [0 : R] definitionally. *)
Global Instance isunitpreserving_plus_abgroup_int_mult (A : AbGroup) (x : A)
  : IsUnitPreserving (Aunit:=zero) (Bunit:=canonical_names.zero)
      (abgroup_int_mult A x)
  := idpath.

(** [abgroup_int_mult R r] preserves addition and zero. *)
Global Instance ismonoidpreserving_plus_abgroup_int_mult (A : AbGroup) (x : A)
  : IsMonoidPreserving (Aop:=(+)) (Bop:=(+)) (abgroup_int_mult A x)
  := {}.

(** [abgroup_int_mult R r] commutes with negation. *)
Definition abgroup_int_mult_neg (A : AbGroup) (x : A) z
  : abgroup_int_mult A x (- z) = - abgroup_int_mult A x z.
Proof.
  snrapply (groups.preserves_negate _); exact _.
Defined.
