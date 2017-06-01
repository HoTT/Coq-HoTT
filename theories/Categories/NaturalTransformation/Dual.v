(** * Opposite natural transformations *)
Require Category.Dual Functor.Dual.
Import Category.Dual.CategoryDualNotations Functor.Dual.FunctorDualNotations.
Require Import Category.Core Functor.Core NaturalTransformation.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

(** ** Definition of [Tᵒᵖ] *)
Definition opposite
           C D
           (F G : Functor C D)
           (T : NaturalTransformation F G)
: NaturalTransformation G^op F^op
  := Build_NaturalTransformation' (G^op) (F^op)
                                  (components_of T)
                                  (fun s d => commutes_sym T d s)
                                  (fun s d => commutes T d s).

Local Notation "T ^op" := (opposite T) : natural_transformation_scope.

(** ** [ᵒᵖ] is judgmentally involutive *)
Local Open Scope natural_transformation_scope.

Definition opposite_involutive C D (F G : Functor C D) (T : NaturalTransformation F G)
: (T^op)^op = T
  := idpath.

Module Export NaturalTransformationDualNotations.
  Notation "T ^op" := (opposite T) : natural_transformation_scope.
End NaturalTransformationDualNotations.
