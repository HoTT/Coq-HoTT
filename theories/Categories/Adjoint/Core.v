(** * Adjunctions *)
Require Import HoTT.Categories.Adjoint.UnitCounit.
Require Import HoTT.Basics.Notations.

Notation Adjunction := AdjunctionUnitCounit.

Module Export AdjointCoreNotations.
  Infix "-|" := Adjunction : type_scope.
End AdjointCoreNotations.
