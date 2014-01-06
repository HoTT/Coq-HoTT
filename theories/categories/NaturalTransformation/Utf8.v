Require Export Category.Utf8 Functor.Utf8.
Require Import NaturalTransformation.Core NaturalTransformation.Composition.Core NaturalTransformation.Dual.

Infix "∘" := compose : natural_transformation_scope.
Infix "∘ˡ" := whisker_l (at level 40, left associativity) : natural_transformation_scope.
Infix "∘ʳ" := whisker_r (at level 40, left associativity) : natural_transformation_scope.

(* This notation should be [only parsing] for now, because otherwise
   copy/paste doesn't work, because the parser doesn't recognize the
   unicode characters [ᵒᵖ].  So, really, this notation is just a
   reminder to do something when Coq's parser is better. *)

Notation "T 'ᵒᵖ'" := (opposite T) (only parsing) : natural_transformation_scope.
Notation "T 'ᵒᵖ''" := (opposite' T) (only parsing) : natural_transformation_scope.
Notation "T 'ᵒᵖ'''" := (opposite_finv T) (at level 3, only parsing) : natural_transformation_scope.
Notation "T 'ᵒᵖ''''" := (opposite_tinv T) (at level 3, only parsing) : natural_transformation_scope.
