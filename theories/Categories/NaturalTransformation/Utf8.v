(** * Unicode notations for natural transformations *)
Require Export Category.Utf8 Functor.Utf8.
Require Import NaturalTransformation.Core NaturalTransformation.Composition.Core NaturalTransformation.Dual.
Require Import Basics.Utf8.

Infix "∘" := compose : natural_transformation_scope.
Infix "∘ˡ" := whisker_l : natural_transformation_scope.
Infix "∘ʳ" := whisker_r : natural_transformation_scope.
Notation "T 'ᵒᵖ'" := (opposite T) : natural_transformation_scope.
