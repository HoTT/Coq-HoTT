(** * Opposite adjunction [F ⊣ G → Gᵒᵖ ⊣ Fᵒᵖ] *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.NaturalTransformation.Core.
Require Import HoTT.Categories.Category.Dual HoTT.Categories.Functor.Dual HoTT.Categories.NaturalTransformation.Dual.
Require Import HoTT.Categories.Adjoint.UnitCounit HoTT.Categories.Adjoint.Core.
Require Import HoTT.Categories.Functor.Identity HoTT.Categories.Functor.Composition.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

(** ** Definition of [Aᵒᵖ] *)
Definition opposite
           C D
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

Local Notation "A ^op" := (opposite A) : adjunction_scope.

Local Open Scope adjunction_scope.

(** ** [ᵒᵖ] is judgmentally involutive *)
Definition opposite_involutive C D (F : Functor C D) (G : Functor D C) (A : F -| G)
: (A^op)^op = A
  := idpath.

Module Export AdjointDualNotations.
  Notation "A ^op" := (opposite A) : adjunction_scope.
End AdjointDualNotations.
