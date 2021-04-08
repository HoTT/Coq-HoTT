(** * Unicode notations for categories *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Category.Morphisms HoTT.Categories.Category.Dual HoTT.Categories.Category.Prod HoTT.Categories.Category.Sum HoTT.Categories.Category.Pi.
Local Set Warnings Append "-notation-overridden".
Require Export HoTT.Categories.Category.Notations.
Local Set Warnings Append "notation-overridden".
Require Import HoTT.Basics.Utf8.

Infix "∘" := compose : morphism_scope.
Notation "m ⁻¹" := (morphism_inverse m) : morphism_scope.
Infix "≅" := Isomorphic : category_scope.
Notation "x ↠ y" := (Epimorphism x y).
Notation "x ↪ y" := (Monomorphism x y).

(** It would be nice to put [, format "C 'ᵒᵖ'"] here, but that makes
    this notation unparseable. *)
Notation "C 'ᵒᵖ'" := (opposite C) : category_scope.

Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..).
Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..) : type_scope.
Notation "∀  x .. y , P" := (pi (fun x => .. (pi (fun y => P)) .. )) : category_scope.
