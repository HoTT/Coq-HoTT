Require Import Category.Core Category.Morphisms Category.Dual Category.Prod Category.Sum.
Require Export Category.Notations.

Infix "∘" := compose (at level 40, left associativity) : morphism_scope.
Notation "m ⁻¹" := (morphism_inverse (m := m)) (at level 3) : morphism_scope.
Infix "≅" := Isomorphic (at level 70, no associativity) : category_scope.
Notation "x ↠ y" := (Epimorphism x y)
                      (at level 99, right associativity, y at level 200).
Notation "x ↪ y" := (Monomorphism x y)
                      (at level 99, right associativity, y at level 200).

(*( This notation should be [only parsing] for now, because otherwise
    copy/paste doesn't work, because the parser doesn't recognize the
    unicode characters [ᵒᵖ].  So, really, this notation is just a
    reminder to do something when Coq's parser is better. *)
Notation "C 'ᵒᵖ'" := (opposite C) (at level 3, only parsing) : category_scope.
