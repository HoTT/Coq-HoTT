(** * Unicode notations for functors *)
Require Export Category.Notations Category.Utf8 Functor.Notations.
Require Import Functor.Core Functor.Composition.Core Functor.Sum Functor.Dual Functor.Identity.
Require Import Basics.Utf8.

Infix "∘" := compose : functor_scope.

Notation "F ₀ x" := (object_of F x) : object_scope.
Notation "F ₁ m" := (morphism_of F m) : morphism_scope.
Notation "F 'ᵒᵖ'" := (opposite F) : functor_scope.
