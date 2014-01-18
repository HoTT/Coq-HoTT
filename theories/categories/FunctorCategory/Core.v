Require Import Category.Core Category.Strict Functor.Core NaturalTransformation.Core Functor.Paths.
(** These must come last, so that [identity], [compose], etc., refer to natural transformations. *)
Require Import NaturalTransformation.Composition.Core NaturalTransformation.Identity NaturalTransformation.Composition.Laws.
Require Import FunextVarieties.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Section functor_category.
  Context `{Funext}.
  Let fs := Funext_downward_closed.

  Variable C : PreCategory.
  Variable D : PreCategory.

  (** There is a category Fun(C, D) of functors from [C] to [D]. *)

  Definition functor_category : PreCategory
    := @Build_PreCategory (Functor C D)
                          (@NaturalTransformation C D)
                          (@identity C D)
                          (@compose C D)
                          (@associativity fs C D)
                          (@left_identity fs C D)
                          (@right_identity fs C D)
                          (fun s d : Functor C D => @Paths.trunc_natural_transformation fs C D s d).
End functor_category.

Local Notation "C -> D" := (functor_category C D) : category_scope.

Lemma isstrict_functor_category `{Funext} C `{IsStrictCategory D}
: IsStrictCategory (C -> D).
Proof.
  typeclasses eauto.
Defined.

Module Export FunctorCategoryCoreNotations.
  (*Notation "C ^ D" := (@functor_category _ D C) : category_scope.
  Notation "[ C , D ]" := (@functor_category _ C D) : category_scope.*)
  Notation "C -> D" := (@functor_category _ C D) : category_scope.
End FunctorCategoryCoreNotations.
