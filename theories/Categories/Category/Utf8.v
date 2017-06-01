(** * Unicode notations for categories *)
Require Import Category.Core Category.Morphisms Category.Dual Category.Prod Category.Sum Category.Pi.
Local Set Warnings Append "-notation-overridden".
Require Export Category.Notations.
Local Set Warnings Append "notation-overridden".

Infix "∘" := compose (at level 40, left associativity) : morphism_scope.
Notation "m ⁻¹" := (morphism_inverse m) (at level 3, format "m '⁻¹'") : morphism_scope.
Infix "≅" := Isomorphic (at level 70, no associativity) : category_scope.
Notation "x ↠ y" := (Epimorphism x y)
                      (at level 99, right associativity, y at level 200).
Notation "x ↪ y" := (Monomorphism x y)
                      (at level 99, right associativity, y at level 200).

(** It would be nice to put [, format "C 'ᵒᵖ'"] here, but that makes
    this notation unparseable. *)
Notation "C 'ᵒᵖ'" := (opposite C) (at level 3) : category_scope.

Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
                              (at level 200, x binder, y binder, right associativity).
Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
                              (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "∀  x .. y , P" := (pi (fun x => .. (pi (fun y => P)) .. ))
                              (at level 200, x binder, y binder, right associativity) : category_scope.
