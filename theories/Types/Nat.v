(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the natural numbers *)

Require Export Coq.Init.Peano.
Require Import HoTT.Basics.
Require Import HoTT.Types.Bool.

(** We reopen these scopes so they take precedence over nat_scope; otherwise, now that we have [Coq.Init.Peano], we'd get [* : nat -> nat -> nat] rather than [* : Type -> Type -> Type]. *)
Global Open Scope type_scope.
Global Open Scope core_scope.

Local Open Scope equiv_scope.

Scheme nat_ind := Induction for nat Sort Type.
Scheme nat_rec := Minimality for nat Sort Type.

