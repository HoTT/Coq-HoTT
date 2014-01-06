Require Import Adjoint.Core Adjoint.Dual Adjoint.Composition.Core.
Require Export Adjoint.Notations.

Infix "⊣" := Adjunction (at level 60, right associativity) : type_scope.

Infix "∘" := compose (at level 40, left associativity) : adjunction_scope.

(* This notation should be [only parsing] for now, because otherwise
   copy/paste doesn't work, because the parser doesn't recognize the
   unicode characters [ᵒᵖ].  So, really, this notation is just a
   reminder to do something when Coq's parser is better. *)

Notation "A 'ᵒᵖ'" := (opposite A) (at level 3, only parsing) : adjunction_scope.
Notation "A 'ᵒᵖ''" := (opposite_inv A) (at level 3, only parsing) : adjunction_scope.
Notation "A 'ᵒᵖ'ᴸ'" := (opposite'L A) (at level 3, only parsing) : adjunction_scope.
Notation "A 'ᵒᵖ'ᴿ'" := (opposite'R A) (at level 3, only parsing) : adjunction_scope.
