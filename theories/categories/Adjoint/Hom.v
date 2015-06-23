(** * Hom-Set Adjunctions *)
Require Import Category.Core Functor.Core.
Require Import Adjoint.Core Adjoint.UnitCounit.
Require Import FunctorCategory.Core Category.Morphisms.
Require Import Category.Dual Functor.Dual.
Require Import Category.Prod Functor.Prod.Core.
Require Import HomFunctor NaturalTransformation.Isomorphisms.
Require Import Functor.Composition.Core.
Require Import FunctorCategory.Morphisms.
Require Import Functor.Identity.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.


Local Open Scope morphism_scope.
Local Open Scope category_scope.
Local Open Scope functor_scope.
Local Open Scope natural_transformation_scope.

Section Adjunction.
  Context `{Funext}.
  Variables C D : PreCategory.
  Variable F : Functor C D.
  Variable G : Functor D C.

  (**
     Quoting the MIT 18.705 Lecture Notes:

     Let [C] and [D] be categories, [F : C → D] and [G : D → C]
     functors. We call [(F, G)] an adjoint pair, [F] the left adjoint
     of [G], and [G] the right adjoint of [F] if, for each object [A :
     C] and object [A' : D], there is a natural bijection

     [Hom_D (F A) A' ≅ Hom_C A (G A')]

     Here natural means that maps [B → A] and [A' → B'] induce a
     commutative diagram:

<<
       Hom_D (F A) A' ≅ Hom_C A (G A')
             |                 |
             |                 |
             |                 |
             |                 |
             V                 V
       Hom_D (F B) B' ≅ Hom_C B (G B')
>>
     *)

  (** We want to [simpl] out the notation machinery *)
  Local Opaque NaturalIsomorphism.

  Let Adjunction_Type := Eval simpl in hom_functor D o (F^op, 1) <~=~> hom_functor C o (1, G).
  (*Let Adjunction_Type := Eval simpl in HomFunctor D ⟨ F ⟨ 1 ⟩ , 1 ⟩ ≅ HomFunctor C ⟨ 1 , G ⟨ 1 ⟩ ⟩.*)
  (*Set Printing All.
  Print Adjunction_Type.*)
  (** Just putting in [Adjunction_Type] breaks [AMateOf] *)

  Record AdjunctionHom :=
    {
      mate_of : @NaturalIsomorphism
                  H
                  (Category.Prod.prod (Category.Dual.opposite C) D)
                  (@Core.set_cat H)
                  (@compose
                     (Category.Prod.prod (Category.Dual.opposite C) D)
                     (Category.Prod.prod (Category.Dual.opposite D) D)
                     (@Core.set_cat H) (@hom_functor H D)
                     (@pair (Category.Dual.opposite C)
                            (Category.Dual.opposite D) D D
                            (@opposite C D F) (identity D)))
                  (@compose
                     (Category.Prod.prod (Category.Dual.opposite C) D)
                     (Category.Prod.prod (Category.Dual.opposite C) C)
                     (@Core.set_cat H) (@hom_functor H C)
                     (@pair (Category.Dual.opposite C)
                            (Category.Dual.opposite C) D C
                            (identity (Category.Dual.opposite C)) G))
    }.
End Adjunction.

Coercion mate_of : AdjunctionHom >-> NaturalIsomorphism.
Bind Scope adjunction_scope with AdjunctionHom.

Arguments mate_of {_} [C%category D%category F%functor G%functor] _%adjunction.
