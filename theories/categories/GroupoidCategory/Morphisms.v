(** * Morphisms in a groupoid *)
Require Import Category.Core Category.Morphisms Category.Univalent GroupoidCategory.Core.
Require Import Trunc Equivalences HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.


Local Open Scope category_scope.

Section groupoid_category.
  Variable X : Type.
  Context `{IsTrunc 1 X}.

  Definition isotoid (s d : groupoid_category X)
  : s <~=~> d -> s = d
    := fun f => f : morphism _ _ _.

  (** ** All groupoids are categories *)
  Global Instance iscategory_groupoid_category
  : IsCategory (groupoid_category X).
  Proof.
    repeat intro.
    apply (isequiv_adjointify (@idtoiso (groupoid_category X) _ _)
                              (@isotoid _ _));
      repeat intro;
      destruct_head @Isomorphic;
      destruct_head @IsIsomorphism;
      compute in *;
      path_induction_hammer.
  Qed.
End groupoid_category.
