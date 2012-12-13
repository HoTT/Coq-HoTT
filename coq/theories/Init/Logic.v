Require Export Notations.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

Inductive False : Prop :=.
Definition not (A : Prop) := A -> False.
Inductive and (A B : Prop) : Prop :=
  conj : A -> B -> and A B.
Definition iff (A B : Prop) := and (A -> B) (B -> A).