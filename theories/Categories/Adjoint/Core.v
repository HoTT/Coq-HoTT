(** * Adjunctions *)
Require Import Adjoint.UnitCounit.
Require Import Basics.Notations.

Notation Adjunction := AdjunctionUnitCounit.

Module Export AdjointCoreNotations.
  Infix "-|" := Adjunction : type_scope.
End AdjointCoreNotations.
