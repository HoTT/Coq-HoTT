(* -*- mode: coq; mode: visual-line -*-  *)
Require Import Basics.
Require Import Types.
Require Import Truncations.
Require Import Algebra.ooGroup.

Local Open Scope path_scope.

(** * Automorphism oo-Groups *)

(** To define the automorphism oo-group [Aut X], we have to construct its classifying space [BAut X]. *)

(** [BAut X] is the type of types that are merely equal to [X]. *)
Definition BAut@{u v} (X : Type@{u}) : Type@{v}
  := sig@{v v} (fun Z => merely (paths@{v} Z X)).

Global Instance ispointed_baut {X : Type} : IsPointed (BAut X) := (X; tr 1).

(** Now we can define [Aut X], since [BAut X] is connected by [is0connected_component]. *)
Definition Aut (X : Type) : ooGroup
  := Build_ooGroup (Build_pType (BAut X) _) _.

(** The type [BAut X] is studied further in [Spaces.BAut] and its subdirectories. *)
