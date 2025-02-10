From HoTT Require Import Basics.Overture Algebra.Groups.Group.

(** Test that opposite groups are definitionally involutive. *)
Fail Definition test1 (G : Group) : G = (grp_op (grp_op G)) :> Group := 1.
