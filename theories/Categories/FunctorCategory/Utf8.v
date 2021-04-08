(** * Unicode notations for functor categories *)
Require Export HoTT.Categories.Category.Utf8 HoTT.Categories.Functor.Utf8 HoTT.Categories.NaturalTransformation.Utf8.
Require Import HoTT.Categories.FunctorCategory.Core HoTT.Categories.FunctorCategory.Morphisms.
Require Import HoTT.Basics.Utf8.

Notation "C → D" := (functor_category C D) : category_scope.
Infix "≅" := NaturalIsomorphism : natural_transformation_scope.
