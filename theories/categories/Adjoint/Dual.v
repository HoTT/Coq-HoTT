(** * Opposite adjunction [F ⊣ G → Gᵒᵖ ⊣ Fᵒᵖ] *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Dual Functor.Dual NaturalTransformation.Dual.
Require Import Adjoint.UnitCounit Adjoint.Core.
Require Import Functor.Identity Functor.Composition.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

Section opposite.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition opposite
             (F : Functor C D)
             (G : Functor D C)
             (A : F -| G)
  : G^op -| F^op
    := @Build_AdjunctionUnitCounit
         _ _ (G^op) (F^op)
         ((counit A)^op)
         ((unit A)^op)
         (unit_counit_equation_2 A)
         (unit_counit_equation_1 A).
End opposite.

Local Notation "A ^op" := (opposite A) (at level 3, format "A '^op'") : adjunction_scope.

Section opposite_involutive.
  Lemma opposite_involutive C D (F : Functor C D) (G : Functor D C) (A : F -| G)
  : ((A^op)^op)%adjunction = A.
  Proof.
    destruct A as [[] [] ? ?].
    reflexivity.
  Defined.
End opposite_involutive.

Module Export AdjointDualNotations.
  Notation "A ^op" := (opposite A) (at level 3, format "A '^op'") : adjunction_scope.
End AdjointDualNotations.
