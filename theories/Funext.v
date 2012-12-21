Require Import Common Paths Contractible Equivalences.

Open Scope path_scope.
Open Scope equiv_scope.

Axiom isequiv_apD10 : forall A B f g, IsEquiv (@apD10 A B f g).
Existing Instance isequiv_apD10.

Definition funext {A : Type} {B : A -> Type} (f g : forall x, B x)
  : (forall x, f x = g x) -> f = g
  := (@apD10 A B f g)^-1.

Axiom funext2 : forall A B (P : A -> B -> Type) (f g : forall x y, P x y),
  (forall x y, f x y = g x y) -> f = g.

Arguments funext2 {A B P} f g _.
