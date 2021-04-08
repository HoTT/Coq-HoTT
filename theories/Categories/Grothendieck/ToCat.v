(** * Grothendieck Construction of a functor to Cat *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.NaturalTransformation.Core.
Require Import HoTT.Categories.Pseudofunctor.Core HoTT.Categories.Pseudofunctor.FromFunctor.
Require Import HoTT.Categories.Cat.Core.
Require Import HoTT.Categories.Grothendieck.PseudofunctorToCat.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section Grothendieck.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  (*Context `{forall C, IsHProp (P C)}.*)
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation cat := (@sub_pre_cat _ P HF).

  Variable C : PreCategory.
  Variable F : Functor C cat.

  (** ** Category of elements *)
  Definition category : PreCategory
    := category (pseudofunctor_of_functor_to_cat F).

  (** ** First projection functor *)
  Definition pr1 : Functor category C
    := pr1 (pseudofunctor_of_functor_to_cat F).
End Grothendieck.
