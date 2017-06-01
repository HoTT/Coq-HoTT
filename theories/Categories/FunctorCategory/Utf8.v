(** * Unicode notations for functor categories *)
Require Export Category.Utf8 Functor.Utf8 NaturalTransformation.Utf8.
Require Import FunctorCategory.Core FunctorCategory.Morphisms.
Require Import Basics.Utf8.

Notation "C → D" := (functor_category C D) : category_scope.
Infix "≅" := NaturalIsomorphism : natural_transformation_scope.
