(* -*- mode: coq; mode: visual-line -*- *)

(** * Theorems about the circle S^1. *)

Require Import Overture PathGroupoids Equivalences Trunc HSet.
Require Import Paths Forall Arrow Universe Empty Unit.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

(* *** Definition of the circle. *)

Module Export Suspension.

Local Inductive Susp (X : Type) : Type :=
  | North : Susp X
  | South : Susp X.

Global Arguments North {X}.
Global Arguments South {X}.

Axiom merid : forall (X : Type) (x : X), North = South :> Susp X.
Global Arguments merid {X} x.

Definition Susp_rect {X : Type} (P : Susp X -> Type)
  (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, (merid x) # H_N = H_S)
: forall (y:Susp X), P y
:= fun y => match y with North => H_N | South => H_S end.

Axiom Susp_comp_merid : forall {X : Type} (P : Susp X -> Type)
  (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, (merid x) # H_N = H_S)
  (x:X),
apD (Susp_rect P H_N H_S H_merid) (merid x) = H_merid x.

End Suspension.
