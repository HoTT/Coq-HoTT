Require Export Category.Utf8 Functor.Core Functor.Composition Functor.Duals.

Infix "∘" := compose_functors : functor_scope.

Notation "F ₀ x" := (object_of F x) (at level 10, no associativity) : object_scope.
Notation "F ₁ m" := (morphism_of F m) (at level 10, no associativity) : morphism_scope.

(* This notation should be [only parsing] for now, because otherwise
   copy/paste doesn't work, because the parser doesn't recognize the
   unicode characters [ᵒᵖ].  So, really, this notation is just a
   reminder to do something when Coq's parser is better. *)

Notation "F ᵒᵖ" := (functor_opposite F) (only parsing) : functor_scope.
Notation "F ᵒᵖ'" := (functor_opposite_inv F) (only parsing, at level 3) : functor_scope.
