Require Export HoTT.Basics.Utf8.
Require Import HoTT.Basics.Overture.

(** * Just enough Utf8/unicode for the Classes library to build, without depending on everything that HoTT.Utf8 depends on. *)

(* Logic *)
Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..) : type_scope.
Notation "∃  x .. y , P" := (exists x, .. (exists y, P) ..) : type_scope.

Notation "x ∧ y" := (x /\ y) : type_scope.
Notation "x → y" := (x -> y) : type_scope.

Notation "x ↔ y" := (x <-> y) : type_scope.
(*Notation "¬ x" := (not x) : type_scope.*)
(*Notation "x ≠ y" := (x <> y) : type_scope.*)

(* Abstraction *)
Notation "'λ'  x .. y , t" := (fun x => .. (fun y => t) ..).
