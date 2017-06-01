(** * Unicode notations for profunctors *)
Require Import Profunctor.Core.
Require Export Profunctor.Notations.
Require Import Basics.Utf8.

Notation "x ⇸ y" := (Profunctor x y) : type_scope.
