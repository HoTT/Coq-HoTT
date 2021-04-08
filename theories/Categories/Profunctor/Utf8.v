(** * Unicode notations for profunctors *)
Require Import HoTT.Categories.Profunctor.Core.
Require Export HoTT.Categories.Profunctor.Notations.
Require Import HoTT.Basics.Utf8.

Notation "x ⇸ y" := (Profunctor x y) : type_scope.
