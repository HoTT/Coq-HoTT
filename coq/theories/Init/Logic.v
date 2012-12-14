(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(*   This file has been modified for the purposes of the HoTT library.  *)
(************************************************************************)

Set Implicit Arguments.

Require Export Notations.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

(** * Propositional connectives *)

(** [True] is the unit type. *)
Inductive True : Type :=
  I : True.

(** [False] is the empty type. *)
Inductive False : Type :=.

(** [not A], written [~A], is the negation of [A] *)
Definition not (A:Type) : Type := A -> False.

Notation "~ x" := (not x) : type_scope.

Notation "'idmap'" := (fun x => x).

Definition compose {A B C : Type} (g : B -> C) (f : A -> B) :=
  fun x => g (f x).

Hint Unfold not: core.

Hint Resolve I : core.
