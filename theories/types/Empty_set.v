(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the empty type *)

Require Import Overture Contractible Funext.
Local Open Scope path_scope.

(** *** Universal mapping property *)

Instance contr_to_Empty_set `{Funext} (A : Type) :
  Contr (Empty_set -> A) :=
  BuildContr _
  (Empty_set_rect A)
  (fun f => path_forall _ f (fun x => Empty_set_rect _ x)).

(** *** Paths *)

(** We could probably prove some theorems about non-existing paths in
   [Empty_set], but this is really quite useless. As soon as an element
   of [Empty_set] is hypothesized, we can prove whatever we like with
   a simple elimination. *)

(** *** HLevel *)

(*** XXX This should go elsewhere *)
Class HProp (A : Type) :=
  { ishprop : forall x y : A, Contr (x = y) }.

Instance hprop_Empty_set : HProp Empty_set :=
  {| ishprop := (fun x y : Empty_set => Empty_set_rect _ x) |}.


