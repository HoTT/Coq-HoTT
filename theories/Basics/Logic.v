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

Require Export Basics.Notations.

Global Set Universe Polymorphism.
Global Set Polymorphic Inductive Cumulativity.
Global Set Asymmetric Patterns.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

(** [True] is the unit type. *)
Inductive True : Set :=
  I : True.

(** [False] is the empty type. *)
Inductive False : Set :=.

#[export] Hint Resolve I : core.

(* In the HoTT library, we generally avoid using [True] and [False] and instead use [Unit] and [Empty]. *)
