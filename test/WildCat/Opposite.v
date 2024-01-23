From HoTT Require Import Basics WildCat.Core WildCat.Opposite.

(* Opposites are (almost) definitionally involutive. *)

Definition test1 A : A = (A^op)^op := 1.
Definition test2 A `{x : IsGraph A} : x = isgraph_op (A := A^op) := 1.
Definition test3 A `{x : Is01Cat A} : x = is01cat_op (A := A^op) := 1.
Definition test4 A `{x : Is2Graph A} : x = is2graph_op (A := A^op) := 1.

(** Is1Cat is not definitionally involutive. *)
Fail Definition test4 A `{x : Is1Cat A} : x = is1cat_op (A := A^op) := 1.
