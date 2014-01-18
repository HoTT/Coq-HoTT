Require Export Category.Utf8 Functor.Utf8 NaturalTransformation.Utf8.
Require Import FunctorCategory.Core FunctorCategory.Morphisms.

Local Open Scope category_scope.

Notation "C → D" := (C -> D)
  (at level 99, D at level 200, right associativity) : category_scope.
Infix "≅" := NaturalIsomorphism : natural_transformation_scope.
