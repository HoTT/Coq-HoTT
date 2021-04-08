Require Import HoTT.Categories.Adjoint.Core HoTT.Categories.Adjoint.Dual HoTT.Categories.Adjoint.Composition.Core.
Require Export HoTT.Categories.Adjoint.Notations.
Require Import HoTT.Basics.Utf8.

Infix "⊣" := Adjunction : type_scope.

Infix "∘" := compose : adjunction_scope.

(** It would be nice to put [, format "A 'ᵒᵖ'"] here, but that would
    make this notation unparseable. *)
Notation "A 'ᵒᵖ'" := (opposite A) : adjunction_scope.
