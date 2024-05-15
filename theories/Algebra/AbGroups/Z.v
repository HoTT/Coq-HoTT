Require Import Basics.
Require Import Spaces.Pos.Core Spaces.BinInt.
Require Import Algebra.AbGroups.AbelianGroup.

(** * The group of integers *)

(** See also Cyclic.v for a definition of the integers as the free group on one generator. *)

Local Open Scope binint_scope.

Section MinimizationToSet.

Local Set Universe Minimization ToSet.

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

End MinimizationToSet.

(** We can multiply by [n : Int] in any abelian group. *)
Definition ab_mul (n : BinInt) {A : AbGroup} : GroupHomomorphism A A.
Proof.
  induction n.
  - exact (grp_homo_compose ab_homo_negation (ab_mul_nat (pos_to_nat p))).
  - exact grp_homo_const.
  - exact (ab_mul_nat (pos_to_nat p)).
Defined.

(** Homomorphisms respect multiplication. *)
Lemma ab_mul_homo {A B : AbGroup} (n : BinInt) (f : GroupHomomorphism A B)
  : grp_homo_compose f (ab_mul n) == grp_homo_compose (ab_mul n) f.
Proof.
  intro x.
  induction n.
  - cbn. refine (grp_homo_inv _ _ @ _).
    refine (ap negate _).
    apply grp_pow_homo.
  - cbn. apply grp_homo_unit.
  - cbn. apply grp_pow_homo.
Defined.

(** Multiplication by zero gives the constant group homomorphism. *)
Definition ab_mul_const `{Funext} {A : AbGroup} : ab_mul 0 (A:=A) = grp_homo_const.
Proof.
  apply equiv_path_grouphomomorphism.
  reflexivity.
Defined.
