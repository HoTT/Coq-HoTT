(** * Unicode notations for natural transformations *)
Require Export HoTT.Categories.Category.Utf8 HoTT.Categories.Functor.Utf8.
Require Import HoTT.Categories.NaturalTransformation.Core HoTT.Categories.NaturalTransformation.Composition.Core HoTT.Categories.NaturalTransformation.Dual.
Require Import HoTT.Basics.Utf8.

Infix "∘" := compose : natural_transformation_scope.
Infix "∘ˡ" := whisker_l : natural_transformation_scope.
Infix "∘ʳ" := whisker_r : natural_transformation_scope.
Notation "T 'ᵒᵖ'" := (opposite T) : natural_transformation_scope.
