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

Require Import Basics.Logic.

Global Set Universe Polymorphism.
Global Set Asymmetric Patterns.
Global Set Primitive Projections.
Global Set Nonrecursive Elimination Schemes.
Local Unset Elimination Schemes.

(** [Option A] is the extension of [A] with an extra element none] *)

Inductive Option (A : Type) : Type :=
| some : A -> Option A
| none : Option A.

Scheme Option_rect := Induction for Option Sort Type.

Arguments some {A} a.
Arguments none {A}.

Register Option as core.option.type.

(** [Sum A B], written [A + B], is the disjoint sum of [A] and [B] *)

Inductive Sum (A B : Type) : Type :=
| inl : A -> Sum A B
| inr : B -> Sum A B.

Scheme Sum_rect := Induction for Sum Sort Type.

Notation "x + y" := (Sum x y) : type_scope.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

(* A notation for coproduct that's less overloaded than [+] *)
Notation "x |_| y" := (Sum x y) (only parsing) : type_scope.

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

Record Prod (A B : Type) := pair { fst : A ; snd : B }.

Scheme Prod_rect := Induction for Prod Sort Type.

Arguments pair {A B} _ _.
Arguments fst {A B} _ / .
Arguments snd {A B} _ / .

Add Printing Let Prod.

Notation "x * y" := (Prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Notation "A /\ B" := (Prod A B) (only parsing) : type_scope.
Notation and := Prod (only parsing).
Notation conj := pair (only parsing).

#[export] Hint Resolve pair inl inr : core.

Definition prod_curry (A B C : Type) (f : A -> B -> C)
  (p : Prod A B) : C := f (fst p) (snd p).

(** [iff A B], written [A <-> B], expresses the equivalence of [A] and [B] *)

Definition iff (A B : Type) := Prod (A -> B) (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.

(** Another way of interpreting booleans as propositions *)

(* Definition is_true b := b = true. *)

(** Polymorphic lists and some operations *)

Inductive list (A : Type) : Type :=
 | nil : list A
 | cons : A -> list A -> list A.

Scheme list_rect := Induction for list Sort Type.

Arguments nil {A}.
Declare Scope list_scope.
Infix "::" := cons : list_scope.
Delimit Scope list_scope with list.
Bind Scope list_scope with list.

Local Open Scope list_scope.
(** Concatenation of two lists *)

Definition app (A : Type) : list A -> list A -> list A :=
  fix app l m :=
  match l with
   | nil => m
   | a :: l1 => a :: app l1 m
  end.

Infix "++" := app : list_scope.
