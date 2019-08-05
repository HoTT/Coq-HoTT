(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import Algebra.ooGroup.

Local Open Scope path_scope.

(** * Actions of oo-Groups *)

Definition ooAction (G : ooGroup)
  := classifying_space G -> Type.

Definition action_space {G} : ooAction G -> Type
  := fun X => X (point _).

Coercion action_space : ooAction >-> Sortclass.
