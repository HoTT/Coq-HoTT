(** * Unicode notations for functors *)
Require Export HoTT.Categories.Category.Notations HoTT.Categories.Category.Utf8 HoTT.Categories.Functor.Notations.
Require Import HoTT.Categories.Functor.Core HoTT.Categories.Functor.Composition.Core HoTT.Categories.Functor.Sum HoTT.Categories.Functor.Dual HoTT.Categories.Functor.Identity.
Require Import HoTT.Basics.Utf8.

Infix "∘" := compose : functor_scope.

Notation "F ₀ x" := (object_of F x) : object_scope.
Notation "F ₁ m" := (morphism_of F m) : morphism_scope.
Notation "F 'ᵒᵖ'" := (opposite F) : functor_scope.
