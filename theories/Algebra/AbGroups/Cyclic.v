Require Import Basics.Overture Basics.Tactics WildCat.Core AbelianGroup
  AbGroups.Z Spaces.Int Groups.QuotientGroup.

(** * Cyclic groups *)

(** The [n]-th cyclic group is the cokernel of [ab_mul n]. *)
Definition cyclic (n : nat) : AbGroup
  := ab_cokernel (ab_mul (A:=abgroup_Z) n).

Definition cyclic_in (n : nat) : abgroup_Z $-> cyclic n
  := grp_quotient_map. 

Definition ab_mul_cyclic_in (n : nat) (x y : abgroup_Z)
  : ab_mul y (cyclic_in n x) = cyclic_in n (y * x)%int.
Proof.
  lhs_V napply ab_mul_natural.
  apply ap, abgroup_Z_ab_mul.
Defined.
