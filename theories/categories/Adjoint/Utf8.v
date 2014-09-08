Require Import Adjoint.Core Adjoint.Dual Adjoint.Composition.Core.
Require Export Adjoint.Notations.

Infix "⊣" := Adjunction (at level 60, right associativity) : type_scope.

Infix "∘" := compose (at level 40, left associativity) : adjunction_scope.

(** It would be nice to put [, format "A 'ᵒᵖ'"] here, but that would
    make this notation unparseable. *)
Notation "A 'ᵒᵖ'" := (opposite A) (at level 3) : adjunction_scope.
Notation "A 'ᵒᵖ''" := (opposite' A) (at level 3) : adjunction_scope.
Notation "A 'ᵒᵖ'ᴸ'" := (opposite'L A) (at level 3) : adjunction_scope.
Notation "A 'ᵒᵖ'ᴿ'" := (opposite'R A) (at level 3) : adjunction_scope.
