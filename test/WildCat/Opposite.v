From HoTT Require Import Basics WildCat.Core WildCat.Opposite.

(** * Opposites are (almost) definitionally involutive. *)

Definition test1 A : A = (A^op)^op :> Type := 1.
Definition test2 A `{x : IsGraph A} : x = @isgraph_op A^op (@isgraph_op A x) := 1.
Definition test3 A `{x : Is01Cat A} : x = @is01cat_op A^op _ (@is01cat_op A _ x) := 1.
Definition test4 A `{x : Is2Graph A} : x = @is2graph_op A^op _ (@is2graph_op A _ x) := 1.

(** [Is1Cat] is not definitionally involutive. *)
Fail Definition test5 A `{x : Is1Cat A} : x = @is1cat_op A^op _ _ _ (@is1cat_op A _ _ _ x) := 1.
