Require Import Spaces.Nat Spaces.Int.
Require Import Algebra.AbGroups.AbelianGroup.

(** * The group of integers *)

(** See also Cyclic.v for a definition of the integers as the free group on one generator. *)

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

(** We can multiply by [n : Int] in any abelian group. *)
Definition ab_mul (n : Int) {A : AbGroup} : GroupHomomorphism A A.
Proof.
  induction n.
  - exact (grp_homo_compose ab_homo_negation (ab_mul_nat (pos_to_nat p))).
  - exact grp_homo_const.
  - exact (ab_mul_nat (pos_to_nat p)).
Defined.

(** Homomorphisms respect multiplication. *)
Lemma ab_mul_homo {A B : AbGroup} (n : Int) (f : GroupHomomorphism A B)
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
