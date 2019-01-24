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

Require Import Logic.

Global Set Universe Polymorphism.
Global Set Asymmetric Patterns.
Global Set Primitive Projections.
Global Set Nonrecursive Elimination Schemes.
Local Unset Elimination Schemes.

(** [option A] is the extension of [A] with an extra element [None] *)

Inductive option (A : Type) : Type :=
  | Some : A -> option A
  | None : option A.

Scheme option_rect := Induction for option Sort Type.

Arguments None [A].

Register option as core.option.type.

(** [sum A B], written [A + B], is the disjoint sum of [A] and [B] *)

Inductive sum (A B : Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.

Scheme sum_rect := Induction for sum Sort Type.

Notation "x + y" := (sum x y) : type_scope.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

(* A notation for coproduct that's less overloaded than [+] *)
Notation "x |_| y" := (sum x y) (only parsing) : type_scope.

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

Record prod (A B : Type) := pair { fst : A ; snd : B }.

Scheme prod_rect := Induction for prod Sort Type.

Arguments pair {A B} _ _.
Arguments fst {A B} _ / .
Arguments snd {A B} _ / .

Add Printing Let prod.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Notation "A /\ B" := (prod A B) (only parsing) : type_scope.
Notation and := prod (only parsing).
Notation conj := pair (only parsing).

Hint Resolve pair inl inr : core.

Definition prod_curry (A B C : Type) (f : A -> B -> C)
  (p : prod A B) : C := f (fst p) (snd p).

(** [iff A B], written [A <-> B], expresses the equivalence of [A] and [B] *)

Definition iff (A B : Type) := prod (A -> B) (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.

(* Natural numbers. *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Scheme nat_rect := Induction for nat Sort Type.

(* It would be nice not to need this, but the tactic [induction] requires it when the target is in [Set], and the above definition of [nat] puts it in [Set]. *)
Scheme nat_rec := Induction for nat Sort Set.

Declare Scope nat_scope.
Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%nat.

Open Scope nat_scope. (* Originally in Peano.v *)


(** [identity A a] is the family of datatypes on [A] whose sole non-empty
    member is the singleton datatype [identity A a a] whose
    sole inhabitant is denoted [refl_identity A a] *)

Inductive identity (A : Type) (a : A) : A -> Type :=
  identity_refl : identity a a.

Scheme identity_rect := Induction for identity Sort Type.

Hint Resolve identity_refl: core.

Arguments identity {A} _ _.
Arguments identity_refl {A a} , [A] a.

Arguments identity_rect [A] a P f y i.


(** Identity type *)

(*
Definition ID := forall A : Type, A -> A.
Definition id : ID := fun A x => x.
*)

Declare Scope identity_scope.
Delimit Scope identity_scope with identity.

Notation "x = y :> A" := (@identity A x y)%identity : identity_scope.

Notation "x = y" := (x = y :>_)%identity : identity_scope.
Notation "x <> y  :> T" := (not (x = y :> T))%identity : identity_scope.
Notation "x <> y" := (x <> y :>_)%identity : identity_scope.

Local Open Scope identity_scope.

(** Another way of interpreting booleans as propositions *)

(* Definition is_true b := b = true. *)

(** Polymorphic lists and some operations *)

Inductive list (A : Type) : Type :=
 | nil : list A
 | cons : A -> list A -> list A.

Scheme list_rect := Induction for list Sort Type.

Arguments nil [A].
Declare Scope list_scope.
Infix "::" := cons (at level 60, right associativity) : list_scope.
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

Infix "++" := app (right associativity, at level 60) : list_scope.
