Require Import Basics.Overture AbelianGroup AbGroups.Z Spaces.Int.

(** * Cyclic groups *)

(** The [n]-th cyclic group is the cokernel of [ab_mul n]. *)
Definition cyclic (n : nat) : AbGroup
  := ab_cokernel (ab_mul (A:=abgroup_Z) n).
