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

  Definition opposite_inv
             (F : Functor C D)
             (G : Functor D C)
             (A : F^op -| G^op)
  : G -| F
    := @Build_AdjunctionUnitCounit
         _ _ G F
         (@opposite_tinv _ _ 1 (F o G) (counit A))
         (@opposite_tinv _ _ (G o F) 1 (unit A))
         (unit_counit_equation_2 A)
         (unit_counit_equation_1 A).

  Definition opposite'R
             (F : Functor C^op D^op)
             (G : Functor D C)
             (A : F -| G^op)
  : G -| F^op'
    := @Build_AdjunctionUnitCounit
         _ _ G (F^op')
         ((counit A)^op')
         ((unit A)^op')
         (unit_counit_equation_2 A)
         (unit_counit_equation_1 A).

  Definition opposite'L
             (F : Functor C D)
             (G : Functor D^op C^op)
             (A : F^op -| G)
  : G^op' -| F
    := @Build_AdjunctionUnitCounit
         _ _ (G^op') F
         ((counit A)^op')
         ((unit A)^op')
         (unit_counit_equation_2 A)
         (unit_counit_equation_1 A).
End opposite.

Local Notation "A ^op" := (opposite A) : adjunction_scope.
Local Notation "A ^op'" := (opposite_inv A) : adjunction_scope.
Local Notation "A ^op'L" := (opposite'L A) (at level 3) : adjunction_scope.
Local Notation "A ^op'R" := (opposite'R A) (at level 3) : adjunction_scope.

Section opposite_involutive.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor C D.
  Variable G : Functor D C.
  Variable A : F -| G.

  Local Notation op_op_id_F := (Functor.Dual.opposite_involutive F).
  Local Notation op_op_id_G := (Functor.Dual.opposite_involutive G).
  Local Notation op_op_id_C := (Category.Dual.opposite_involutive C).
  Local Notation op_op_id_D := (Category.Dual.opposite_involutive D).

  Lemma opposite_involutive
  : match
      op_op_id_F as Fop in (_ = F), op_op_id_G as Gop in (_ = G)
      return
      F -| G
    with
      | idpath, idpath
        => match
          op_op_id_C as Cop in (_ = C), op_op_id_D as Dop in (_ = D)
          return
          (match Cop in (_ = C), Dop in (_ = D) return Functor C D with
             | idpath, idpath => (F^op)^op
           end
             -|
             match Dop in (_ = D), Cop in (_ = C) return Functor D C with
               | idpath, idpath => (G^op)^op
             end)
        with
          | idpath, idpath
            => ((A^op)^op)%adjunction
        end
    end = A.
  Proof.
    destruct A as [[] [] ? ?], F, G, C, D.
    reflexivity.
  Defined.
End opposite_involutive.

Module Export AdjointDualNotations.
  Notation "A ^op" := (opposite A) : adjunction_scope.
  Notation "A ^op'" := (opposite_inv A) : adjunction_scope.
  Notation "A ^op'L" := (opposite'L A) (at level 3) : adjunction_scope.
  Notation "A ^op'R" := (opposite'R A) (at level 3) : adjunction_scope.
End AdjointDualNotations.
