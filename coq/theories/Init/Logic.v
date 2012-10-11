Require Export Notations.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

Inductive True : Type := I.