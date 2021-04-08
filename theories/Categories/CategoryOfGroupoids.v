(** * Groupoid, the precategory of strict groupoid categories *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.Category.Strict.
Require Import HoTT.Categories.Cat.Core.
Require Import HoTT.Categories.GroupoidCategory.Core.
Require Import HoTT.Categories.Functor.Paths.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

Section groupoid_cat.
  Context `{Funext}.

  Let P : PreCategory -> Type
    := fun C => IsGroupoid C /\ IsStrictCategory C.
  Let HF : forall C D, P C -> P D -> IsHSet (Functor C D)
    := fun C D HC HD => @trunc_functor _ C D _ (snd HD) _.

  (** There is a full precategory of [cat] which is the strict groupoid precategories *)

  Definition groupoid_cat : PreCategory
    := @sub_pre_cat _ P HF.
End groupoid_cat.
