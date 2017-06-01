Require Import Adjoint.Core Adjoint.Dual Adjoint.Composition.Core.
Require Export Adjoint.Notations.
Require Import Basics.Utf8.

Infix "⊣" := Adjunction : type_scope.

Infix "∘" := compose : adjunction_scope.

(** It would be nice to put [, format "A 'ᵒᵖ'"] here, but that would
    make this notation unparseable. *)
Notation "A 'ᵒᵖ'" := (opposite A) : adjunction_scope.
