Require Import Adjoint.UnitCounit.

Notation Adjunction := AdjunctionUnitCounit.

Module Export AdjointCoreNotations.
  Infix "-|" := Adjunction (at level 60, right associativity) : type_scope.
End AdjointCoreNotations.
