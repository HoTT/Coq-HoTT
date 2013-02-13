(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the empty type *)

Require Import Overture Contractible.
Local Open Scope path_scope.

Inductive Empty : Type :=.

Definition not (A:Type) : Type := A -> False.

(** *** Universal mapping property *)

Instance contr_to_Empty `{Funext} (A : Type) :
  Contr (Empty -> A) :=
  BuildContr _
  (Empty_rect A)
  (fun f => path_forall _ f (fun x => Empty_rect _ x)).

(** *** Paths *)

(** We could probably prove some theorems about non-existing paths in
   [Empty], but this is really quite useless. As soon as an element
   of [Empty] is hypothesized, we can prove whatever we like with
   a simple elimination. *)

(** *** HLevel *)

(*** XXX This should go elsewhere *)
Class HProp (A : Type) :=
  { ishprop : forall x y : A, Contr (x = y) }.

Instance hprop_Empty : HProp Empty :=
  {| ishprop := (fun x y : Empty => Empty_rect _ x) |}.


