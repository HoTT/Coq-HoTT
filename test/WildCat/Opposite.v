From HoTT Require Import Basics WildCat.Core WildCat.Opposite WildCat.Equiv.

(** * Opposites are definitionally involutive. *)

Definition test1 A : A = (A^op)^op :> Type := 1.
Definition test2 A `{x : IsGraph A} : x = @isgraph_op A^op (@isgraph_op A x) := 1.
Definition test3 A `{x : Is01Cat A} : x = @is01cat_op A^op _ (@is01cat_op A _ x) := 1.
Definition test4 A `{x : Is2Graph A} : x = @is2graph_op A^op _ (@is2graph_op A _ x) := 1.
Definition test5 A `{x : Is1Cat A} : x = @is1cat_op A^op _ _ _ (@is1cat_op A _ _ _ x) := 1.

(** * [core] only partially commutes with taking the opposite category. *)
Definition core1 A `{HasEquivs A} : (core A)^op = core A^op :> Type := 1.
Definition core2 A `{HasEquivs A} : isgraph_op (A:=core A) = isgraph_core (A:=A^op) := 1.
Definition core3 A `{HasEquivs A} : is01cat_op (A:=core A) = is01cat_core (A:=A^op) := 1.
Definition core4 A `{HasEquivs A} : is2graph_op (A:=core A) = is2graph_core (A:=A^op) := 1.

(** This also passes, but we comment it out as it is slow.  When uncommented, to save time, we end with [Admitted.] instead of [Defined.] *)

Opaque compose_catie_isretr.
Time Definition core5 A `{HasEquivs A} : is1cat_op (A:=core A) = is1cat_core (A:=A^op) := 1.
(* 0.07s (or 0.3s without the Opaque line). *)
